/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Opposite.Triangle
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Appendix.Mathlib.CategoryTheory.Triangulated.Opposite.Basic

/-!
# The (pre)triangulated structure on the opposite category

Addendum to the mathlib file.

-/

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

variable (C : Type*) [Category C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Pretriangulated

open Opposite

variable {C}

lemma distinguished_iff_op (T : Triangle C) :
    (T ∈ distTriang C) ↔
      ((triangleOpEquivalence C).functor.obj (Opposite.op T)) ∈ distTriang Cᵒᵖ := by
  constructor
  · intro hT
    exact op_distinguished _ hT
  · intro hT'
    exact isomorphic_distinguished _ (unop_distinguished _ hT') _
      (((triangleOpEquivalence C).unitIso.app (Opposite.op T)).unop.symm)

variable [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C]

instance : (opOp C).IsTriangulated where
  map_distinguished T hT := by
    rw [mem_distTriang_op_iff']
    refine ⟨_, op_distinguished T hT, ⟨?_⟩⟩
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · aesop_cat
    · aesop_cat
    · dsimp
      simp only [Functor.map_id, comp_id, id_comp,
        opOp_commShiftIso_hom_app T.obj₁ _ _ (add_neg_cancel 1),
        opShiftFunctorEquivalence_counitIso_inv_app _ _ _ (add_neg_cancel 1),
        shiftFunctorCompIsoId_op_hom_app _ _ _ (add_neg_cancel 1),
        shiftFunctor_op_map _ _ (add_neg_cancel 1),
        shiftFunctor_op_map _ _ (neg_add_cancel 1)]
      simp only [Functor.op_obj, Opposite.unop_op, unop_id, Functor.map_id, op_id, id_comp,
        Iso.hom_inv_id_app, comp_id,
        Functor.id_obj, Functor.comp_obj, assoc, Iso.inv_hom_id_app_assoc, op_comp,
        Quiver.Hom.unop_op,
        Iso.op_hom_inv_id_app_assoc,
        assoc, unop_comp, Functor.map_comp]
      slice_rhs 2 3 =>
        rw [← op_comp, ← op_comp, ← Functor.map_comp, ← unop_comp, Iso.inv_hom_id_app]
      simp only [Functor.op_obj, Opposite.unop_op, unop_id, Functor.map_id, op_id, id_comp, assoc]
      slice_rhs 1 2 =>
        rw [← op_comp, ← op_comp]
        erw [← NatTrans.naturality]
      dsimp
      simp only [assoc, shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app]
      slice_rhs 2 3 =>
        rw [← op_comp, ← op_comp, Iso.inv_hom_id_app]
      simp

noncomputable instance : (opOpEquivalence C).inverse.CommShift ℤ :=
  (inferInstance : (opOp C).CommShift ℤ)

noncomputable instance : (opOpEquivalence C).functor.CommShift ℤ :=
  (opOpEquivalence C).commShiftFunctor ℤ

noncomputable instance : (unopUnop C).CommShift ℤ :=
  (inferInstance : (opOpEquivalence C).functor.CommShift ℤ)

instance : (opOpEquivalence C).CommShift ℤ := (opOpEquivalence C).commShift_of_inverse ℤ

instance : (opOp C).IsTriangulated := inferInstance

end Pretriangulated

end CategoryTheory
