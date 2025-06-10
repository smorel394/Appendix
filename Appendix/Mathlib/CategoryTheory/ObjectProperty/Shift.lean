/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# Properties of objects on categories equipped with shift

Addendum to the mathlib file.

-/

open CategoryTheory Category

namespace CategoryTheory

variable {C : Type*} [Category C] (P Q : ObjectProperty C)
  {A : Type*} [AddMonoid A] [HasShift C A]

namespace ObjectProperty

/-- `P : ObjectProperty C` is stable under the shift by `a : A` if
`P X` implies `P X⟦a⟧`. -/
class IsStableUnderShiftBy (a : A) : Prop where
  le_shift : P ≤ P.shift a

lemma le_shift (a : A) [P.IsStableUnderShiftBy a] :
    P ≤ P.shift a := IsStableUnderShiftBy.le_shift

instance (a : A) [P.IsStableUnderShiftBy a] :
    P.isoClosure.IsStableUnderShiftBy a where
  le_shift := by
    rintro X ⟨Y, hY, ⟨e⟩⟩
    exact ⟨Y⟦a⟧, P.le_shift a _ hY, ⟨(shiftFunctor C a).mapIso e⟩⟩

instance (a : A) [P.IsStableUnderShiftBy a]
    [Q.IsStableUnderShiftBy a] : (P ⊓ Q).IsStableUnderShiftBy a where
  le_shift _ hX :=
    ⟨P.le_shift a _ hX.1, Q.le_shift a _ hX.2⟩

variable (A) in
/-- `P : ObjectProperty C` is stable under the shift by `A` if
`P X` implies `P X⟦a⟧` for any `a : A`. -/
class IsStableUnderShift where
  isStableUnderShiftBy (a : A) : P.IsStableUnderShiftBy a := by infer_instance

attribute [instance] IsStableUnderShift.isStableUnderShiftBy

instance [P.IsStableUnderShift A] :
    P.isoClosure.IsStableUnderShift A where

instance [P.IsStableUnderShift A]
    [Q.IsStableUnderShift A] : (P ⊓ Q).IsStableUnderShift A where

lemma prop_shift_iff_of_isStableUnderShift {G : Type*} [AddGroup G] [HasShift C G]
    [P.IsStableUnderShift G] [P.IsClosedUnderIsomorphisms] (X : C) (g : G) :
    P (X⟦g⟧) ↔ P X := by
  refine ⟨fun hX ↦ ?_, P.le_shift g _⟩
  rw [← P.shift_zero G, ← P.shift_shift g (-g) 0 (by simp)]
  exact P.le_shift (-g) _ hX

end ObjectProperty

end CategoryTheory
