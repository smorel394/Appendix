/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # The mapping cone of a morphism of cochain complexes

Addendum to mathlib file.

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Limits

variable {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]

omit [Preadditive C] in
@[simp]
lemma CategoryTheory.Limits.biprod.is_zero_iff
    [HasZeroMorphisms C] (A B : C)
    [HasBinaryBiproduct A B] : IsZero (biprod A B) ↔ IsZero A ∧ IsZero B := by
  constructor
  · intro h
    simp only [IsZero.iff_id_eq_zero]
    constructor
    · rw [← cancel_mono (biprod.inl : _ ⟶ A ⊞ B)]
      apply h.eq_of_tgt
    · rw [← cancel_mono (biprod.inr : _ ⟶ A ⊞ B)]
      apply h.eq_of_tgt
  · rintro ⟨hA, hB⟩
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext
    · apply hA.eq_of_tgt
    · apply hB.eq_of_tgt

namespace CochainComplex

open HomologicalComplex

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)
variable [HasHomotopyCofiber φ]

namespace mappingCone

open HomComplex

@[simp]
lemma isZero_X_iff (i : ℤ) :
    IsZero ((mappingCone φ).X i) ↔ IsZero (F.X (i + 1)) ∧ IsZero (G.X i) := by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ i (i + 1) rfl
  erw [(homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).isZero_iff,
    CategoryTheory.Limits.biprod.is_zero_iff]

lemma to_break {X : C} {n : ℤ} (x : X ⟶ (mappingCone φ).X n) (p : ℤ) (hp : n + 1 = p) :
    ∃ (x₁ : X ⟶ F.X p) (x₂ : X ⟶ G.X n), x = x₁ ≫ (mappingCone.inl φ).v p n (by omega) +
      x₂ ≫ (mappingCone.inr φ).f n :=
  ⟨x ≫ (mappingCone.fst φ).1.v n p hp, x ≫ (mappingCone.snd φ).v n n (by omega),
    by simp [ext_to_iff φ _ _ hp]⟩

/-- The composition `φ ≫ mappingCone.inr φ` is homotopic to `0`. -/
noncomputable def inrCompHomotopy :
    Homotopy (φ ≫ inr φ) 0 :=
  homotopyCofiber.inrCompHomotopy φ (fun n => ⟨n - 1, by simp⟩)

end mappingCone

end CochainComplex
