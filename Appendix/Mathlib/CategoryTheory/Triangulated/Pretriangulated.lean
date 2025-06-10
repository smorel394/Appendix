/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw, Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Pretriangulated Categories

Appendix to the mathlib file.

-/

assert_not_exists TwoSidedIdeal

noncomputable section

open CategoryTheory Preadditive Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory

namespace Limits

-- should be moved to a better place
namespace BinaryBiproductData

variable {C : Type _} [Category C]
    {X₁ X₂ : C} [HasZeroMorphisms C] [HasBinaryBiproduct X₁ X₂] (d : BinaryBiproductData X₁ X₂)

def isoBiprod {C : Type _} [Category C]
    {X₁ X₂ : C} [HasZeroMorphisms C] [HasBinaryBiproduct X₁ X₂] (d : BinaryBiproductData X₁ X₂) :
    X₁ ⊞ X₂ ≅ d.bicone.pt :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X₁ X₂) d.isBilimit.isLimit

@[reassoc (attr := simp)]
lemma isoBiprod_inv_fst : d.isoBiprod.inv ≫ biprod.fst = d.bicone.fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ d.isBilimit.isLimit ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
lemma isoBiprod_inv_snd : d.isoBiprod.inv ≫ biprod.snd = d.bicone.snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ d.isBilimit.isLimit ⟨WalkingPair.right⟩

@[reassoc (attr := simp)]
lemma isoBiprod_hom_fst : d.isoBiprod.hom ≫ d.bicone.fst = biprod.fst := by
  rw [← isoBiprod_inv_fst, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma isoBiprod_hom_snd : d.isoBiprod.hom ≫ d.bicone.snd = biprod.snd := by
  rw [← isoBiprod_inv_snd, Iso.hom_inv_id_assoc]

end BinaryBiproductData

end Limits

end CategoryTheory

namespace CategoryTheory

open Category Pretriangulated ZeroObject

/-
We work in a preadditive category `C` equipped with an additive shift.
-/
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]

namespace Pretriangulated

variable [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor C n)] [hC : Pretriangulated C]

variable {C}

namespace Triangle

variable (T : Triangle C)

lemma shift_distinguished_iff (n : ℤ) :
    (CategoryTheory.shiftFunctor (Triangle C) n).obj T ∈ (distTriang C) ↔ T ∈ distTriang C := by
  constructor
  · intro hT
    exact isomorphic_distinguished _ (shift_distinguished _ hT (-n)) _
      ((shiftEquiv (Triangle C) n).unitIso.app T)
  · intro hT
    exact shift_distinguished T hT n

end Triangle

@[simps! hom_hom₁ hom_hom₃ inv_hom₁ inv_hom₃]
def isoTriangleOfIso₁₃ (T₁ T₂ : Triangle C) (hT₁ : T₁ ∈ distTriang C)
    (hT₂ : T₂ ∈ distTriang C) (e₁ : T₁.obj₁ ≅ T₂.obj₁) (e₃ : T₁.obj₃ ≅ T₂.obj₃)
    (comm : T₁.mor₃ ≫ (shiftFunctor C 1).map e₁.hom = e₃.hom ≫ T₂.mor₃) :
      T₁ ≅ T₂ := by
  have h := exists_iso_of_arrow_iso _ _ (inv_rot_of_distTriang _ hT₁)
    (inv_rot_of_distTriang _ hT₂)
    (Arrow.isoMk ((shiftFunctor C (-1)).mapIso e₃) e₁ (by
      dsimp
      simp only [comp_neg, neg_comp, assoc, neg_inj, ← Functor.map_comp_assoc, ← comm]
      simp only [Functor.map_comp, assoc]
      erw [← NatTrans.naturality]
      rfl))
  let e := h.choose
  refine Triangle.isoMk _ _ e₁ (Triangle.π₃.mapIso e) e₃ ?_ ?_ comm
  · refine e.hom.comm₂.trans ?_
    congr 1
    exact h.choose_spec.2
  · rw [← cancel_mono ((shiftFunctorCompIsoId C (-1) 1 (neg_add_cancel 1)).inv.app T₂.obj₃)]
    rw [assoc, assoc]
    refine Eq.trans ?_ e.hom.comm₃
    rw [h.choose_spec.1]
    dsimp
    erw [assoc, ← NatTrans.naturality]
    rfl

end Pretriangulated

end CategoryTheory
