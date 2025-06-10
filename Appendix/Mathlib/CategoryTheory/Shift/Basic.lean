/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin, Andrew Yang, Joël Riou
-/
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Discrete

/-!
# Shift

Addendum to the mathlib file.

-/

namespace CategoryTheory

noncomputable section

universe v u

variable (C : Type u) (A : Type*) [Category.{v} C]

attribute [local instance] endofunctorMonoidalCategory

variable {A C}

section Defs

variable (A C) [AddMonoid A]

section
variable [HasShift C A]

open Functor.Monoidal

@[simp]
lemma shiftFunctorZero'_eq_shiftFunctorZero :
    shiftFunctorZero' C (0 : A) rfl = shiftFunctorZero C A := by
  ext1
  dsimp only [shiftFunctorZero']
  simp

end

end Defs

section AddCommMonoid

variable [AddCommMonoid A] [HasShift C A]

variable (X Y : C) (f : X ⟶ Y)

variable {X Y}

lemma shiftFunctorComm_hom_app_of_add_eq_zero (m n : A) (hmn : m + n = 0) (X : C) :
    (shiftFunctorComm C m n).hom.app X =
      (shiftFunctorCompIsoId C m n hmn).hom.app X ≫
        (shiftFunctorCompIsoId C n m (by rw [add_comm, hmn])).inv.app X := by
  dsimp only [shiftFunctorCompIsoId]
  simp only [Functor.comp_obj, shiftFunctorComm_eq C m n 0 hmn, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.id_obj, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Iso.hom_inv_id_app_assoc]

lemma shiftFunctorComm_inv_app_of_add_eq_zero (m n : A) (hmn : m + n = 0) (X : C) :
    (shiftFunctorComm C m n).inv.app X =
      (shiftFunctorCompIsoId C n m (by rw [add_comm, hmn])).hom.app X ≫
      (shiftFunctorCompIsoId C m n hmn).inv.app X := by
  dsimp only [shiftFunctorCompIsoId]
  simp only [Functor.comp_obj, shiftFunctorComm_eq C m n 0 hmn, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.id_obj, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_app_assoc]

end AddCommMonoid

end

end CategoryTheory
