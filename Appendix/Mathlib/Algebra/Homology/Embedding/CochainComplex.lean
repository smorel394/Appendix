/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Appendix.Mathlib.Algebra.Homology.Embedding.ComplementaryTrunc
import Appendix.Mathlib.Algebra.Homology.Embedding.TruncLE

/-!
# Truncations on cochain complexes indexed by the integers.

Addendum to the mathlib file.

-/

open CategoryTheory Category Limits ComplexShape ZeroObject

namespace CochainComplex

variable {C : Type*} [Category C]

open HomologicalComplex

section HasZeroMorphisms

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

section

variable [HasZeroObject C] [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]

lemma isIso_ιTruncLE_f (n m : ℤ) (h : m < n) : IsIso ((K.ιTruncLE n).f m) := by
  obtain ⟨a, rfl⟩ : ∃ a, (embeddingUpIntLE n).f a = m := by
    obtain ⟨a, ha⟩ := Int.le.dest h.le
    exact ⟨a, by dsimp; omega⟩
  apply HomologicalComplex.isIso_ιTruncLE_f
  simp only [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
  rintro rfl
  simp at h

lemma isIso_πTruncGE_f (n m : ℤ) (h : n < m) : IsIso ((K.πTruncGE n).f m) := by
  obtain ⟨a, rfl⟩ : ∃ a, (embeddingUpIntGE n).f a = m := by
    obtain ⟨a, ha⟩ := Int.le.dest h.le
    exact ⟨a, by dsimp; omega⟩
  apply HomologicalComplex.isIso_πTruncGE_f
  simp only [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
  rintro rfl
  simp at h

end

end HasZeroMorphisms

section HasZeroMorphisms

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
  (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [∀ (i : ℤ), K.HasHomology i] [∀ (i : ℤ), L.HasHomology i] (n : ℤ)

instance : QuasiIsoAt (K.πTruncGE n) n :=
  K.quasiIsoAt_πTruncGE (embeddingUpIntGE n) (j := 0) (by simp)

instance : QuasiIsoAt (K.ιTruncLE n) n :=
  K.quasiIsoAt_ιTruncLE (embeddingUpIntLE n) (j := 0) (by simp)

noncomputable def truncGEXIso (n : ℤ) (i : ℤ) (hi : n < i) :
    (K.truncGE n).X i ≅ K.X i :=
  HomologicalComplex.truncGEXIso K (embeddingUpIntGE n) (i := (i - n).natAbs) (by
      dsimp
      rw [Int.natAbs_of_nonneg (by omega), add_sub_cancel])
    (fun h => by
      rw [boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero] at h
      linarith)

noncomputable def truncGEXIsoOpcycles (n : ℤ) :
    (K.truncGE n).X n ≅ K.opcycles n :=
  HomologicalComplex.truncGEXIsoOpcycles K (embeddingUpIntGE n) (i := 0) (by simp)
    (by rw [boundaryGE_embeddingUpIntGE_iff])

lemma acyclic_truncGE_iff (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (K.truncGE n₁).Acyclic ↔ K.IsLE n₀ := by
  dsimp [truncGE]
  rw [acyclic_truncGE_iff_isSupportedOutside,
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h).isSupportedOutside₂_iff]

end HasZeroMorphisms

section Abelian

variable [Abelian C] (K L : CochainComplex C ℤ)

/-- The cokernel sequence of the monomorphism `K.ιTruncLE n`. -/
noncomputable abbrev shortComplexTruncLE (n : ℤ) : ShortComplex (CochainComplex C ℤ) :=
  HomologicalComplex.shortComplexTruncLE K (embeddingUpIntLE n)

lemma shortComplexTruncLE_shortExact (n : ℤ) :
    (K.shortComplexTruncLE n).ShortExact := by
  apply HomologicalComplex.shortComplexTruncLE_shortExact

variable (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

/-- The canonical morphism `(K.shortComplexTruncLE n₀).X₃ ⟶ K.truncGE n₁`. -/
noncomputable abbrev shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE n₀).X₃ ⟶ K.truncGE n₁ :=
  HomologicalComplex.shortComplexTruncLEX₃ToTruncGE K
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h)

@[reassoc (attr := simp)]
lemma g_shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE n₀).g ≫ K.shortComplexTruncLEX₃ToTruncGE n₀ n₁ h = K.πTruncGE n₁ := by
  apply HomologicalComplex.g_shortComplexTruncLEX₃ToTruncGE

lemma acyclic_truncLE_iff (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (K.truncLE n₀).Acyclic ↔ K.IsGE n₁ := by
  dsimp [truncLE]
  rw [acyclic_truncLE_iff_isSupportedOutside,
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h).isSupportedOutside₁_iff K]

end Abelian

end CochainComplex
