/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Triangulated functors

Addendum to the mathlib file.

-/

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Pretriangulated Preadditive

namespace Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
  (F : C ⥤ D) [F.CommShift ℤ] (G : D ⥤ E) [G.CommShift ℤ]

attribute [local simp] map_zsmul comp_zsmul zsmul_comp
  commShiftIso_zero commShiftIso_add
  shiftFunctorAdd'_eq_shiftFunctorAdd
  commShiftIso_comp_hom_app

variable [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor E n).Additive]
  [Pretriangulated C] [Pretriangulated D] [Pretriangulated E]

lemma map_distinguished_iff [F.IsTriangulated] [Full F] [Faithful F] (T : Triangle C) :
    (F.mapTriangle.obj T ∈ distTriang D) ↔ T ∈ distTriang C := by
  constructor
  · intro hT
    obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle T.mor₁
    refine isomorphic_distinguished _ mem _ (F.mapTriangle.preimageIso ?_)
    exact isoTriangleOfIso₁₂ _ _ hT (F.map_distinguished _ mem) (Iso.refl _) (Iso.refl _)
      (by simp)
  · exact F.map_distinguished T

lemma isTriangulated_iff_comp_right {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] [NatTrans.CommShift e.hom ℤ]
    [G.IsTriangulated] [Full G] [Faithful G] :
    F.IsTriangulated ↔ H.IsTriangulated := by
  rw [← isTriangulated_iff_of_iso e]
  constructor
  · intro
    infer_instance
  · intro
    constructor
    intro T hT
    rw [← G.map_distinguished_iff]
    exact isomorphic_distinguished _ ((F ⋙ G).map_distinguished T hT) _
      ((mapTriangleCompIso F G).symm.app T)

end Functor

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
  [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

open Triangulated

section

variable {C D : Type _} [Category C] [Category D]
  [HasShift C ℤ] [HasShift D ℤ] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ]

lemma IsTriangulated.of_fully_faithful_triangulated_functor
    [F.IsTriangulated] [F.Full] [F.Faithful] [IsTriangulated D] :
    IsTriangulated C where
  octahedron_axiom {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃} comm
    {v₁₂ w₁₂} h₁₂ {v₂₃ w₂₃} h₂₃ {v₁₃ w₁₃} h₁₃ := by
    have comm' : F.map u₁₂ ≫ F.map u₂₃ = F.map u₁₃ := by rw [← comm, F.map_comp]
    have H := Triangulated.someOctahedron comm' (F.map_distinguished _ h₁₂)
      (F.map_distinguished _ h₂₃) (F.map_distinguished _ h₁₃)
    exact
      ⟨{
        m₁ := F.preimage H.m₁
        m₃ := F.preimage H.m₃
        comm₁ := F.map_injective (by simpa using H.comm₁)
        comm₂ := F.map_injective (by
          rw [← cancel_mono ((F.commShiftIso (1 : ℤ)).hom.app X₁)]
          simpa using H.comm₂)
        comm₃ := F.map_injective (by simpa using H.comm₃)
        comm₄ := F.map_injective (by
          rw [← cancel_mono ((F.commShiftIso (1 : ℤ)).hom.app X₂)]
          simpa using H.comm₄)
        mem := by
          rw [← F.map_distinguished_iff]
          simpa using H.mem }⟩

end

end CategoryTheory
