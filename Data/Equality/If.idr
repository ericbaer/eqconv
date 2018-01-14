||| Utilities for proofs on functions involving if statements.
module Data.Equality.If

import Data.So

%access public export
%default total

------------------------------------------------------------------------------
-- Stupid little lemmas that are either in the standard library but I can't
-- find them, or that I should be able to replace with more basic primitives
------------------------------------------------------------------------------

||| Applies `not` to both sides of an equality, and reduces
notTrueIsFalse : not x = True -> x = False
notTrueIsFalse {x=True}  Refl impossible
notTrueIsFalse {x=False} notx = Refl

||| a and (not a) is a contradiction
boolANotA : {a : Bool} -> a = True -> not a = True -> Void
boolANotA {a = True}  aTrue aFalse = trueNotFalse $ sym aFalse
boolANotA {a = False} aTrue aFalse = trueNotFalse $ sym aTrue

||| Equality of `Nat`s implies equality of their predecessors
decRefl : S m = S n -> m = n
decRefl Refl = Refl

||| Inequality of `Nat`s implies inequality of their predecessors
decNot : Not (S m = S n) -> Not (m = n)
decNot nSmSn = \mn => nSmSn $ cong {f=S} mn

||| Double negation elimination
dneNot : Not (Not (Not a)) -> Not a
dneNot = flip (.) (flip Prelude.Basics.apply)

trueVoidIsFalse : Not (a = True) -> a = False
trueVoidIsFalse {a=False} _ = Refl
trueVoidIsFalse {a=True}  n = absurd $ n Refl

falseVoidIsTrue : Not (a = False) -> a = True
falseVoidIsTrue {a=False} n = absurd $ n Refl
falseVoidIsTrue {a=True}  _ = Refl

------------------------------------------------------------------------------
-- Stupid little lemmas on LTE
-----------------------------------------------------------------------------

||| `pred` preserves `Not` `LTE`
decNotLTE : Not (LTE (S a) (S b)) -> Not (LTE a b)
decNotLTE nlteSaSb = \lteab => nlteSaSb $ LTESucc lteab

||| Construct an `LTE` given proof that its inverse does not exist
flipNotLTE : {a, b : Nat} -> Not (LTE (S b) a) -> LTE a b
flipNotLTE {a=Z}   {b=Z}   nsbLTEa = LTEZero
flipNotLTE {a=Z}   {b=S n} nsbLTEa = LTEZero
flipNotLTE {a=S m} {b=Z}   nsbLTEa = absurd $ nsbLTEa $ LTESucc LTEZero
flipNotLTE {a=S m} {b=S n} nsbLTEa = LTESucc $ flipNotLTE $ decNotLTE nsbLTEa

------------------------------------------------------------------------------
-- Stupid little lemmas on So
-----------------------------------------------------------------------------

-- Can't rewrite the So itself with a Refl for some reason
||| One thing that's convenient about booleans instead of propositional logic:
||| double negation elimination is trivial
dneSo : {a : Bool} -> So (not (not a)) -> So a
dneSo {a = True}  Oh = Oh
dneSo {a = False} Oh impossible

ohRefl : So x -> (x = True)
ohRefl Oh = Refl

reflOh : (x = True) -> So x
reflOh Refl = Oh

ohNotRefl : So (not x) -> (x = False)
ohNotRefl {x=True}  Oh impossible
ohNotRefl {x=False} Oh = Refl

soANotA : So a -> So (not a) -> Void
soANotA a na = boolANotA (ohRefl a) (ohRefl na)

||| So not False implies Not So False
soNotToNotSo : So (not x) -> Not (So x)
soNotToNotSo snox = \sox => soANotA sox snox

||| Not So False implies So not False    
notSoToSoNot : Not (So x) -> So (not x)
notSoToSoNot {x=False} _ = Oh
notSoToSoNot {x=True} nx = absurd $ nx Oh

||| Contrapositive using `So`
copoSo : (So x -> y) -> Not y -> So (not x)
copoSo soxy ny = notSoToSoNot $ ny . soxy

------------------------------------------------------------------------------
-- Utilities for working with if statements
------------------------------------------------------------------------------

||| Any function can distribute across the two limbs of an if statement
ifDistrib :  {b, c : ty} -> {f : ty -> ty2}
          -> f (if a then b else c) = if a then f b else f c
ifDistrib {a=True}  = Refl
ifDistrib {a=False} = Refl

||| Reduce an if statement given that the condition is true
reduceTrueIf :  cond = True
             -> ifThenElse cond (Delay l) (Delay r) = thing
             -> l = thing
reduceTrueIf Refl Refl = Refl

||| Reduce an if statement given that the condition is false
reduceFalseIf :  cond = False
              -> ifThenElse cond (Delay l) (Delay r) = thing
              -> r = thing
reduceFalseIf Refl Refl = Refl

||| Reconstruct an if statement given that the condition is true
expandTrueIf :  cond = True
             -> l = thing
             -> ifThenElse cond (Delay l) (Delay r) = thing
expandTrueIf Refl Refl = Refl

||| Reconstruct an if statement given that the condition is false
expandFalseIf :  cond = False
              -> r = thing
              -> ifThenElse cond (Delay l) (Delay r) = thing
expandFalseIf Refl Refl = Refl

------------------------------------------------------------------------------
-- Converting compare a b = GT to/from So (a > b) and similar
------------------------------------------------------------------------------

implementation Uninhabited (LT = EQ) where uninhabited Refl impossible
implementation Uninhabited (Prelude.Interfaces.LT = GT) where
    uninhabited Refl impossible
implementation Uninhabited (EQ = GT) where uninhabited Refl impossible

compareEQToSoNotGT : {a, b : Nat} -> compare a b = EQ -> So (not (a > b))
compareEQToSoNotGT {a} {b} refl with (compare a b)
    | LT = absurd refl
    | EQ = Oh
    | GT = absurd $ sym refl

compareGTToSoGT : {a, b : Nat} -> compare a b = GT -> So (a > b)
compareGTToSoGT {a} {b} refl with (compare a b)
    | LT = absurd refl
    | EQ = absurd refl
    | GT = Oh

soGTToCompareGT : {a, b : Nat} -> So (a > b) -> compare a b = GT
soGTToCompareGT {a} {b} oh with (compare a b)
    | LT = absurd $ soANotA Oh oh
    | EQ = absurd $ soANotA Oh oh
    | GT = Refl

------------------------------------------------------------------------------
-- Random lemmas relating to `compare`
------------------------------------------------------------------------------

implementation DecEq Ordering where
    decEq LT LT = Yes Refl
    decEq LT EQ = No uninhabited
    decEq LT GT = No uninhabited
    decEq EQ LT = No $ uninhabited . sym
    decEq EQ EQ = Yes Refl
    decEq EQ GT = No uninhabited
    decEq GT LT = No $ uninhabited . sym
    decEq GT EQ = No $ uninhabited . sym
    decEq GT GT = Yes Refl

||| If a + 1 is greater than (equal to, less than) b + 1, then
||| a is greater than (equal to, less than) b
predPreservesCompare : compare (S a) (S b) = x -> compare a b = x
predPreservesCompare {a} {b} {x} refl with (compare a b)
    | x' with (decEq x x')
        | Yes xx' = refl
        | No nxx' = absurd $ nxx' $ sym refl

||| If a is greater than (or equal to, less than) b, then
||| a + 1 is greater than (or equal or, less than) b + 1
succPreservesCompare : compare a b = x -> compare (S a) (S b) = x
succPreservesCompare {a} {b} {x} refl with (compare (S a) (S b))
    | x' with (decEq x x')
        | Yes xx' = refl
        | No nxx' = absurd $ nxx' $ sym refl

------------------------------------------------------------------------------
-- Converting compare a b = GT to/from LTE (S b) a
------------------------------------------------------------------------------

lteToCompareLT : {a, b : Nat} -> LTE (S b) a -> compare b a = LT
lteToCompareLT {a=Z}   {b=Z}   lte           impossible
lteToCompareLT {a=Z}   {b=S m} lte           impossible
lteToCompareLT {a=S m} {b=Z}   lte           = Refl
lteToCompareLT {a=S m} {b=S n} (LTESucc lte) = lteToCompareLT lte
    
lteToCompareGT : {a, b : Nat} -> LTE (S b) a -> compare a b = GT
lteToCompareGT {a=Z}   {b=Z}   lte           impossible
lteToCompareGT {a=Z}   {b=S m} lte           impossible
lteToCompareGT {a=S m} {b=Z}   lte           = Refl
lteToCompareGT {a=S m} {b=S n} (LTESucc lte) = lteToCompareGT lte

||| Converts evidence of the result of `compare` into `LTE`
compareGTToLTE : {a, b : Nat} -> compare a b = GT -> LTE (S b) a
compareGTToLTE {a=Z}   {b=Z}   Refl impossible
compareGTToLTE {a=Z}   {b=S n} Refl impossible
compareGTToLTE {a=S m} {b=Z}   Refl = LTESucc LTEZero
compareGTToLTE {a=S m} {b=S n} refl =
    LTESucc $ compareGTToLTE $ predPreservesCompare refl

------------------------------------------------------------------------------
-- Converting LTE to/from So
------------------------------------------------------------------------------

||| Convert `So` to `LTE` evidence
soGTToLTE : So (a > b) -> LTE (S b) a
soGTToLTE oh = compareGTToLTE $ soGTToCompareGT oh

||| Convert `LTE` evidence to `So`
lteToSoGT : LTE (S b) a -> So (a > b)
lteToSoGT lte = compareGTToSoGT $ lteToCompareGT lte

||| Converse of `soGTToLTE`: converts the `No` result of `isLTE` into a `So`
notLTEToNotSo : Not (LTE (S b) a) -> So (not (a > b))
notLTEToNotSo nsbLTEa = notSoToSoNot $ nsbLTEa . soGTToLTE

------------------------------------------------------------------------------
-- Utilities for working with if statements
------------------------------------------------------------------------------

||| Reduce an if statement on a greater-than equality condition, given
||| evidence for the greater-than
reduceLTEIfGT :  LTE (S b) a
              -> ifThenElse (a > b) (Delay l) (Delay r) = thing
              -> l = thing
reduceLTEIfGT bLTEa ifThing = reduceTrueIf (ohRefl $ lteToSoGT bLTEa) ifThing

||| Expands an equality into an if statement on a greater-than equality
||| condition, given evidence for the greater-than
expandLTEIfGT :  LTE (S b) a
              -> l = thing
              -> ifThenElse (a > b) (Delay l) (Delay r) = thing
expandLTEIfGT bLTEa thing = expandTrueIf (ohRefl $ lteToSoGT bLTEa) thing

||| Equality between an if statement on a true condition, and its first limb
ifTrue : a = True -> ifThenElse a (Delay b) (Delay c) = b
ifTrue Refl = Refl

||| Equality between an if statement on a false condition, and its second limb
ifFalse : a = False -> ifThenElse a (Delay b) (Delay c) = c
ifFalse Refl = Refl

||| Equality between an if statement on a greater-than condition, and its
||| first limb, given evidence that the condition is true
lteIfGT :  {l, r : ty} 
        -> LTE (S b) a -> ifThenElse (a > b) (Delay l) (Delay r) = l
lteIfGT lte = ifTrue $ ohRefl $ lteToSoGT lte

||| Equality between an if statement on a greater-than condition, and its
||| second limb, given evidence that the condition is false
notLTEIfGT :  {l, r : ty}
           -> Not (LTE (S b) a) -> ifThenElse (a > b) (Delay l) (Delay r) = r
notLTEIfGT nlte = ifFalse $ ohNotRefl $ notLTEToNotSo nlte

||| If the result of an if statement is the then limb, and we know that the
||| two limbs are unequal, then the condition must be true.
thenTrue : Not (b = c) -> ifThenElse a (Delay b) (Delay c) = b -> a = True
thenTrue {a} {b} {c} not_bc if_abc_b with (decEq a True)
    | Yes atrue = atrue
    | No antrue with (ifFalse {a} {b} {c} $ trueVoidIsFalse antrue)
        | if_abc_c = absurd $ not_bc $ trans (sym if_abc_b) if_abc_c

||| If the result of an if statement is the else limb, and we know that the
||| two limbs are unequal, then the condition must be false
elseFalse : Not (b = c) -> ifThenElse a (Delay b) (Delay c) = c -> a = False
elseFalse {a} {b} {c} not_bc if_abc_c with (decEq a False)
    | Yes afalse = afalse
    | No anfalse with (ifTrue {a} {b} {c} $ falseVoidIsTrue anfalse)
        | if_abc_b = absurd $ not_bc $ trans (sym if_abc_b) if_abc_c
