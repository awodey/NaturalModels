(* natural models *)

Unset Automatic Introduction.
Require Ktheory.Elements.
Require Import Ktheory.Utilities.
Require Import RezkCompletion.precategories 
               RezkCompletion.yoneda
               RezkCompletion.category_hset
               RezkCompletion.functors_transformations.
Require Import Foundations.hlevel2.hSet.

Import RezkCompletion.pathnotations.PathNotations
       Ktheory.Utilities.Notation.

Module Import Notation.
  Notation Hom := precategory_morphisms.
  Notation "b ← a" := (precategory_morphisms a b) (at level 50).
  Notation "a → b" := (precategory_morphisms a b) (at level 50).
  Notation "a ==> b" := (functor a b) (at level 50).
  Notation "f ;; g" := (precategories.compose f g) (at level 50, only parsing).
  Notation "g ∘ f" := (precategories.compose f g) (at level 50, only parsing).
  Notation "# F" := (functor_on_morphisms F) (at level 3).
  Notation "C '^op'" := (opp_precat C) (at level 3).
  Notation SET := hset_precategory.
End Notation.

Definition fiber
{ C : precategory }
{ P Q : C^op ==> SET }
( f : nat_trans P Q)
( q : Elements.cat Q )
: C^op ==> SET .

Proof. intros. refine (tpair _ _ _).
  { refine (tpair _ _ _).
    { intros c.
      refine (tpair _ _ _). 
      { exact( total2 ( fun p : Elements.cat P
                                        => Hom (Elements.cat_on_nat_trans f p) q )).
