||| Conversion to/from propositional/boolean equality/inequality
module Data.Equality.Conversion

import Data.So
import Control.Isomorphism

import Data.Equality.If

%access public export
%default total

------------------------------------------------------------------------------
-- Forcing use of default implementation
------------------------------------------------------------------------------

||| An interface for interfaces that have default (unnamed) implementations
-- Tried making this variadic in i, but it broke ForceImpl
interface HasDefaultImpl (i : Type -> Type) (ty : Type) where
    DefaultImpl : i ty

implementation HasDefaultImpl Eq ()      where DefaultImpl = %implementation
implementation HasDefaultImpl Eq Bool    where DefaultImpl = %implementation
implementation HasDefaultImpl Eq Nat     where DefaultImpl = %implementation
implementation HasDefaultImpl Eq String  where DefaultImpl = %implementation
implementation HasDefaultImpl Eq Integer where DefaultImpl = %implementation

||| Pattern-matching on Impl Refl in a function body forces the implementation
||| of some interface to be the default interface (i.e. the caller of the
||| function can't pass in a named interface)
data ForceImpl :  (i : Type -> Type) -> (ty : Type) -> i ty -> Type where
    Impl :  (HasDefaultImpl i ty)
         => {someImpl : i ty}
         -> (refl : someImpl = DefaultImpl)
         -> ForceImpl i ty someImpl
       
------------------------------------------------------------------------------
-- The interface itself
------------------------------------------------------------------------------

||| Conversion from propositional equality & inequality. Minimal definition is
||| is ((decToBool_ || boolToNot_) && (notToBool_ && boolToDec_)); the ones
||| involving equalities rather than inequalities are usually easier to write.
||| (Sort of a step towards VerifiedEq, I guess.)
||| 
||| Putting the Eq constraint on the methods rather than the interface head
||| avoids problems at call sites trying to convince the compiler that two
||| different pieces of evidence were constructed under the same Eq
||| implementation.
|||
||| Implementors should pattern match on {good = Impl Refl} to convince the
||| compiler that the default Eq k implementation is used in your function
||| body, otherwise you'll get errors complaining of inability to unify
||| a /= b = True and True = True.
interface (DecEq k) => EqConv k where
    decToBool_ :  (eq : Eq k)
               => {good : ForceImpl Eq k eq}
               -> {a, b : k}
               -> (a = b) -> (a == b = True)
    decToBool_ {good} {a=x} {b=x} Refl with (choose $ x == x)
        | Right oh = absurd $ boolToNot_ {good} (ohRefl oh) Refl
        | Left  oh = ohRefl oh

    notToBool_ :  (eq : Eq k)
               => {good : ForceImpl Eq k eq}
               -> {a, b : k}
               -> Not (a = b) -> not (a == b) = True
    notToBool_ {good} {a=x} {b=y} nxy with (choose $ not (x == y))
        | Right oh = absurd $ nxy $ boolToDec_ {good} $ ohRefl $ dneSo oh
        | Left  oh = ohRefl oh

    boolToDec_ :  (eq : Eq k)
               => {good : ForceImpl Eq k eq}
               -> {a, b : k}
               -> (a == b = True) -> (a = b)
    boolToDec_ {good} {a=x} {b=y} xyTrue with (decEq x y)
        | Yes eq = eq
        | No neq = absurd $ boolANotA xyTrue (notToBool_ {good} neq) 

    boolToNot_ :  (eq : Eq k)
               => {good : ForceImpl Eq k eq}
               -> {a, b : k}
               -> not (a == b) = True -> Not (a = b)
    boolToNot_ {good} {a=x} {b=y} notXyTrue =
        \xy => absurd $ boolANotA (decToBool_ {good} xy) notXyTrue
    
------------------------------------------------------------------------------
-- Implementations that aren't just plain old cheating
-- These could probably be derived automatically
------------------------------------------------------------------------------

implementation EqConv () where
    decToBool_ {good=Impl Refl} {a=()} {b=()} Refl = Refl
    notToBool_ {good=Impl Refl} {a=()} {b=()} nab = absurd $ nab Refl

implementation EqConv Bool where
    decToBool_ {good=Impl Refl} {a=True}  {b=False} Refl impossible
    decToBool_ {good=Impl Refl} {a=False} {b=True}  Refl impossible
    decToBool_ {good=Impl Refl} {a=True}  {b=True}  Refl = Refl
    decToBool_ {good=Impl Refl} {a=False} {b=False} Refl = Refl

    notToBool_ {good=Impl Refl} {a=True}  {b=True}  nab = absurd $ nab Refl
    notToBool_ {good=Impl Refl} {a=False} {b=False} nab = absurd $ nab Refl
    notToBool_ {good=Impl Refl} {a=True}  {b=False} nab = Refl
    notToBool_ {good=Impl Refl} {a=False} {b=True}  nab = Refl

implementation EqConv Nat where
    decToBool_ {good=Impl Refl} {a=Z}   {b=Z}   Refl = Refl
    decToBool_ {good=Impl Refl} {a=Z}   {b=S n} Refl impossible
    decToBool_ {good=Impl Refl} {a=S m} {b=Z}   Refl impossible
    -- why do I have to recurse instead of just matching the
    -- (a = b) Refl and {a=S m} {b = S m}, thus solving instantly?
    decToBool_ {good=Impl Refl} {a=S m} {b=S n} refl =
        decToBool_ {good=Impl Refl} {a=m} {b=n} $ decRefl refl

    notToBool_ {good=Impl Refl} {a=Z}   {b=Z}   nab = absurd $ nab Refl
    notToBool_ {good=Impl Refl} {a=Z}   {b=S n} nab = Refl
    notToBool_ {good=Impl Refl} {a=S n} {b=Z}   nab = Refl
    notToBool_ {good=Impl Refl} {a=S m} {b=S n} nab =
        notToBool_ {good=Impl Refl} {a=m} {b=n} $ decNot nab
  
------------------------------------------------------------------------------
-- Implementations on primitive types. They work fine! Really, believe me!
------------------------------------------------------------------------------

implementation EqConv String where
    decToBool_ {good=Impl Refl} {a=x} {b=y} xy =
        case x == y of
            True  => primitiveEq
            False => absurd $ primitiveNotEq xy
        where primitiveEq : a = b
              primitiveEq = really_believe_me (Refl {x})
              postulate primitiveNotEq : a = b -> Void
        
    notToBool_ {good=Impl Refl} {a=x} {b=y} nxy =
        case x == y of
            True  => absurd $ nxy primitiveEq
            False => primitiveEq
        where primitiveEq : a = b
              primitiveEq = really_believe_me (Refl {x})
              postulate primitiveNotEq : a = b -> Void
             
implementation EqConv Int where
    decToBool_ {good=Impl Refl} {a=x} {b=y} xy = 
        case x == y of
            True  => primitiveEq
            False => absurd $ primitiveNotEq xy
        where primitiveEq : a = b
              primitiveEq = really_believe_me (Refl {x})
              postulate primitiveNotEq : a = b -> Void

    notToBool_ {good=Impl Refl} {a=x} {b=y} nxy =
        case x == y of
            True  => absurd $ nxy primitiveEq
            False => primitiveEq
        where primitiveEq : a = b
              primitiveEq = really_believe_me (Refl {x})
              postulate primitiveNotEq : a = b -> Void
            
------------------------------------------------------------------------------
-- Convenience synonyms to avoid {auto good} in interface definition
------------------------------------------------------------------------------

||| To prevent choking on {auto good} in an interface definition
decToBool :  (eq : Eq k, EqConv k)
          => {auto good : ForceImpl Eq k eq}
          -> {a, b : k} -> (a = b) -> (a == b = True)               
decToBool {good} = decToBool_ {good}

||| To prevent choking on {auto good} in an interface definition
notToBool :  (eq : Eq k, EqConv k)
          => {auto good : ForceImpl Eq k eq}
          -> {a, b : k} -> Not (a = b) -> not (a == b) = True
notToBool {good} = notToBool_ {good}

||| To prevent choking on {auto good} in an interface definition
boolToDec :  (eq : Eq k, EqConv k)
          => {auto good : ForceImpl Eq k eq}
          -> {a, b : k} -> (a == b) = True -> (a = b)
boolToDec {good} = boolToDec_ {good}

||| To prevent choking on {auto good} in an interface definition
boolToNot :  (eq : Eq k, EqConv k)
          => {auto good : ForceImpl Eq k eq}
          -> {a, b : k} -> not (a == b) = True -> Not (a = b)
boolToNot {good} = boolToNot_ {good}

------------------------------------------------------------------------------
-- Wrapped evidence of inequality
------------------------------------------------------------------------------

||| Evidence of an inequality under some definition of Eq. This has to be its
||| own data type, rather than a type function, since the whole point of using
||| (a /= b = True) instead of Not (a = b) as the evidence of inequality is so
||| we can have decidable equality on data types which contain this evidence
||| type, and you can't have a DecEq implementation on a type function (since
||| there's no guarantee the type function is injective, unlike Haskell where
||| there's a strict division between not-necessarily-injective type families
||| and definitely-injective type synonyms).
data Neq : k -> k -> Type where
    MkNeq : (Eq k) => {a, b : k} -> not (a == b) = True -> Neq a b

||| Equality of equalities.
reflUnique : (x : a = b) -> (y : a = b) -> (x = y)
reflUnique Refl Refl = Refl

||| Equality of inequalities. Can't do this with Nots, absent extensionality.
neqUnique : (Eq k) => {a, b : k} -> (x : Neq a b) -> (y : Neq a b) -> (x = y)
neqUnique (MkNeq xrefl) (MkNeq yrefl) = cong $ reflUnique xrefl yrefl

||| Converting from propositional inequality to Neq evidence
notToNeq :  (eq : Eq k, EqConv k)
         => {auto good : ForceImpl Eq k eq}
         -> {a, b : k} -> Not (a = b) -> Neq a b
notToNeq nab = MkNeq $ notToBool nab

------------------------------------------------------------------------------
-- Utilities for working with if statements
------------------------------------------------------------------------------

||| Reduce an if statement on an equality condition, given that the values
||| being tested are the same
reduceReflIf :  (Eq k, EqConv k) => {a, c : k}
             -> a = c
             -> ifThenElse (a == c) (Delay l) (Delay r) = thing
             -> l = thing
reduceReflIf {a} {c} ac ifThing = reduceTrueIf (decToBool ac) ifThing

||| Reduce an if statement on an equality condition, given that the values
||| being tested are not the same
reduceNotIf :  (Eq k, EqConv k) => {a, c : k}
            -> Not (a = c)
            -> ifThenElse (a == c) (Delay l) (Delay r) = thing
            -> r = thing
reduceNotIf nac ifThing =
    reduceFalseIf (notTrueIsFalse $ notToBool nac) ifThing

||| Reconstruct an if statement on an equality condition, given that the values
||| being tested are the same
expandReflIf :  (Eq k, EqConv k) => {a, c : k}
             -> a = c
             -> l = thing
             -> ifThenElse (a == c) (Delay l) (Delay r) = thing
expandReflIf ac lthing = expandTrueIf (decToBool ac) lthing

||| Reconstruct an if statement on an equality condition, given that the values
||| being tested are not the same
expandNotIf :  (Eq k, EqConv k) => {a, c : k}
            -> Not (a = c)
            -> r = thing
            -> ifThenElse (a == c) (Delay l) (Delay r) = thing
expandNotIf nac rthing =
    expandFalseIf (notTrueIsFalse $ notToBool nac) rthing
   
------------------------------------------------------------------------------
-- Other random lemmas
------------------------------------------------------------------------------

||| Double negation elimination using `EqConv`
dne : (Eq ty, EqConv ty) => {a, b : ty} -> Not (Not (a = b)) -> a = b
dne = boolToDec . ohRefl . dneSo . reflOh . convOuter . convInner where

    convInner : Not (Not (a = b)) -> Not (not (a == b) = True)
    convInner nnab = nnab . boolToNot

    eliminateLhsEq : {x : Bool} -> not (x == True) = y -> not x = y
    eliminateLhsEq {x=True}  Refl = Refl
    eliminateLhsEq {x=False} Refl = Refl
        
    convOuter : Not (not (a == b) = True) -> not (not (a == b)) = True
    convOuter = eliminateLhsEq . notToBool

