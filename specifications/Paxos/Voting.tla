------------------------------- MODULE Voting ------------------------------- 
(***************************************************************************)
(* This is a high-level algorithm in which a set of processes              *)
(* cooperatively choose a value.                                           *)
(***************************************************************************)
EXTENDS Integers  (* 注意，paxos 里面的 PN，这里叫做 Ballot*)
-----------------------------------------------------------------------------
                    \*Value跟Chosen是两码事
CONSTANT Value,     \* The set of choosable values.

         Acceptor,  \* A set of processes that will choose a value.  
         Quorum     \* The set of "quorums", where a quorum" is a 
                    \*   "large enough" set of acceptors

(***************************************************************************)
(* Here are the assumptions we make about quorums.                         *)
(***************************************************************************)
ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* Ballot is a set of "ballot numbers".  For simplicity, we let it be the  *)
(* set of natural numbers.  However, we write Ballot for that set to       *)
(* distinguish ballots from natural numbers used for other purposes.       *)
(***************************************************************************)
Ballot == Nat   \*Ballot即pn，可以不是自然数，能比较大小接口。这里简化为自然数
-----------------------------------------------------------------------------
(***************************************************************************)
(* In the algorithm, each acceptor can cast one or more votes, where each  *)
(* vote cast by an acceptor has the form <<b, v>> indicating that the      *)
(* acceptor has voted for value v in ballot b.  A value is chosen if a     *)
(* quorum of acceptors have voted for it in the same ballot.               *)
(***************************************************************************)


(***************************************************************************)
(* The algorithm's variables.                                              *)
(***************************************************************************)
\*votes[a] 表示 a投过的票，  MaxBal[a]表示a见过的最大Ballot(PN)
VARIABLE votes,   \* votes[a] is the set of votes cast by acceptor a
         maxBal   \* maxBal[a] is a ballot number.  Acceptor a will cast
                  \*   further votes only in ballots numbered \geq maxBal[a]

\*每个acceptor可以为多个proposal投票, \X表示笛卡尔积 Cartesian product
(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now make a series of definitions an assert some simple theorems      *)
(* about those definitions that lead to the algorithm.                     *)
(***************************************************************************)
\*a voted for <b,v>  <b, v>，元组, ordered tuples，
VotedFor(a, b, v) == <<b, v>> \in votes[a]
  (*************************************************************************)
  (* True iff acceptor a has voted for v in ballot b.                      *)
  (*************************************************************************)

  \*v has been ChosenAt b 存在一个Quorum Q，其中每个成员都为(b,v)投票了，也就是形成了决议  
ChosenAt(b, v) == \E Q \in Quorum : 
                     \A a \in Q : VotedFor(a, b, v)
  (*************************************************************************)
  (* True iff a quorum of acceptors have all voted for v in ballot b.      *)
  (*************************************************************************)
  \* chosen是决议选中的值。那么肯定有个v，在Ballot为b时被chosen了。这个是动态产生的集合，不是保存在变量里面
chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}
  (*************************************************************************)
  (* The set of values that have been chosen.                              *)
  (*************************************************************************)
  \* a DidNotVoteAt b, a 没有为Ballot b投票，那么就是对任意v，都没有投过
DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v) 
\* 为什么不是>=? 应该是认为不会有相同的Ballot的，paxos要求distinct set，各个server不会用相同的PN
\* 这里没有考虑v, 只是说b。
\*如果DidNotVoteAt(a,b)不成立，就是曾经为b投过某个v，那么就允许再投(b,v)？ 、 TODO: 感觉paxos没有这一条，只比较PN
CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)
  (*************************************************************************)
  (* Because acceptor a will not cast any more votes in a ballot numbered  *)
  (* < maxBal[a], this implies that a has not and will never cast a vote   *)
  (* in ballot b.                                                          *)
  (*************************************************************************)
  \* 不可能用b来 chose v以外的值。 对于除v以外的任意值w，不可能被用Ballot b choose了。因为Quorum里面，已经投了(b,v)或者不能为b投了
  \*说的是存在一个quorum，满足，并非任意一个都满足。
NoneOtherChoosableAt(b, v) == 
   \E Q \in Quorum :
     \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)
  (*************************************************************************)
  (* If this is true, then ChosenAt(b, w) is not and can never become true *)
  (* for any w # v.                                                        *)
  (*************************************************************************)
  \* 不可能用 <=b的ballot chose v以外的值。但是用更大的ballot是可以的，Phase 2的正常情况
  \* 实际上表示 <b, v>形成了定论。后面只能增加Ballot，不能改变v了。  实际上这个对应 P2b?
SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)
  (*************************************************************************)
  (* If this is true, then no value other than v has been or can ever be   *)
  (* chosen in any ballot numbered less than b.                            *)
  (*************************************************************************)
  \* 在ballot 0时的安全性，啥含义？  
-----------------------------------------------------------------------------
THEOREM AllSafeAtZero == \A v \in Value : SafeAt(0, v)
-----------------------------------------------------------------------------
\* 一旦选中一个，就不能在有别的可选中了
THEOREM ChoosableThm ==
          \A b \in Ballot, v \in Value : 
             ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
-----------------------------------------------------------------------------
\* 这个隐含了啥？ 跟前面的  CannotVoteAt 关联理解。注意，这里没有说chosen，只是说VotedFor(a, b, v)，就能保证SafeAt(b, v)了。
VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
                 VotedFor(a, b, v) => SafeAt(b, v)
\* 从投票角度，如果同一个Server a，为同一个b投了两次，那么一定是相同的value
\*ToDo: a1和a1，如果同一个b，是否也是同一value?
OneVote == \A a \in Acceptor, b \in Ballot, v, w \in Value : 
              VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

\*这个也是从检查vote 开始的，没有任何关于proposal的内容。就是关注如何保证从vote以后的事情
OneValuePerBallot ==  
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
       VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)
-----------------------------------------------------------------------------

THEOREM OneValuePerBallot => OneVote
-----------------------------------------------------------------------------
\* 这个实际上保证的，就是Consensus的最简单的模型：要么没有形成决议，要么只有一个决议。不过这里又称为Consistency了
THEOREM VotesSafeImpliesConsistency ==
          /\ TypeOK 
          /\ VotesSafe
          /\ OneVote
          => \/ chosen = {}
             \/ \E v \in Value : chosen = {v}
-----------------------------------------------------------------------------
\* Q, b, v三个参数
ShowsSafeAt(Q, b, v) == 
  /\ \A a \in Q : maxBal[a] \geq b
  /\ \E c \in -1..(b-1) : 
      /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
-----------------------------------------------------------------------------
THEOREM ShowsSafety == 
          TypeOK /\ VotesSafe /\ OneValuePerBallot =>
             \A Q \in Quorum, b \in Ballot, v \in Value :
               ShowsSafeAt(Q, b, v) => SafeAt(b, v)
 
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now write the specification.  The initial condition is               *)
(* straightforward.                                                        *)
(***************************************************************************)
\* 初始化： 每个server的votes都是空集合，maxBal都是 -1
Init == /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]


(***************************************************************************)
(* Next are the actions that make up the next-state action.                *)
(*                                                                         *)
(* An acceptor a is allowed to increase maxBal[a] to a ballot number b at  *)
(* any time.                                                               *)
(***************************************************************************)
\* 必须大于当前的maxBal，然后仅仅修改该server的。相等则不变
IncreaseMaxBal(a, b) ==
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
  /\ UNCHANGED votes

(***************************************************************************)
(* Next is the action in which acceptor a votes for v in ballot b.  The    *)
(* first four conjuncts re enabling conditions.  The first maintains the   *)
(* requirement that the acceptor cannot cast a vote in a ballot less than  *)
(* maxBal[a].  The next two conjuncts maintain the invariance of           *)
(* OneValuePerBallot.  The fourth conjunct maintains the invariance of     *)
(* VotesSafe.                                                              *)
(***************************************************************************)
VoteFor(a, b, v) ==
    /\ maxBal[a] \leq b                 \* a的Ballot <= b，根据下面条件，实际上不可能等于
    /\ \A vt \in votes[a] : vt[1] # b   \* a 没有为ballot b投票过
    /\ \A c \in Acceptor \ {a} :        \* 除了a之外的其他server，如果投过Ballot b，那么一定是value b
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]


(***************************************************************************)
(* The next-state action and the invariant.                                *)
(***************************************************************************)
\* Next要不就是修改某个server的Ballot，要不就Vote，即只能执行phase 或者 phase 2?
\* Voting这个里面，没有关于Propose的步骤，只从Vote这一步开始。
Next  ==  \E a \in Acceptor, b \in Ballot : 
            \/ IncreaseMaxBal(a, b)
            \/ \E v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal>>

Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot
-----------------------------------------------------------------------------
THEOREM Invariance == Spec => []Inv
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following statement instantiates module Consensus with the constant *)
(* Value of this module substituted for the constant Value of module       *)
(* Consensus, and the state function `chosen' defined in this module       *)
(* substituted for the variable `chosen' of module Value.  More precisely, *)
(* for each defined identifier id of module Value, this statement defines  *)
(* C!id to equal the value of id under these substitutions.                *)
(***************************************************************************)
C == INSTANCE Consensus
\* Consensus模块的各种常量和变量，有同名的都替代了。比如chosen，就是用voting 模块中的chosen替代. 所以， chosen同时满足voting和consensus两个模块中的约束
\* 下面这些是TLA+ proof，参见http://lamport.azurewebsites.net/pubs/keappa08-web.pdf
THEOREM Spec => C!Spec 
<1>1. Inv /\ Init => C!Init
<1>2. Inv /\ [Next]_<<votes, maxBal>> => [C!Next]_chosen
<1>3. QED
  <2>1. []Inv /\ [][Next]_<<votes, maxBal>> => [][C!Next]_chosen
    BY <1>2 \* and temporal reasoning
  <2>2. []Inv /\ Spec => C!Spec
    BY <2>1, <1>1
  <2>3. QED
    BY <2>2, Invariance
=============================================================================

