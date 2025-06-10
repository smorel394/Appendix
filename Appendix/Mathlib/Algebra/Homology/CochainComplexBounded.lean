/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Appendix.Mathlib.CategoryTheory.Shift.CommShift


/-!
# C^b

-/

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category C]

protected def bounded [HasZeroMorphisms C] : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ (n : ℤ), K.IsStrictlyLE n ∧ ∃ (m : ℤ), K.IsStrictlyGE m

instance [HasZeroMorphisms C] : (CochainComplex.bounded C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ e ⟨n, _, m, _⟩
    exact ⟨n, isStrictlyLE_of_iso e n, m, isStrictlyGE_of_iso e m⟩

abbrev Bounded [HasZeroMorphisms C] :=
  (CochainComplex.bounded C).FullSubcategory

namespace Bounded

section

variable [HasZeroMorphisms C]

def ι : Bounded C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

def fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

instance : (ι C).Full := ObjectProperty.full_ι _
instance : (ι C).Faithful := ObjectProperty.faithful_ι _

variable {C} in
def quasiIso [CategoryWithHomology C] : MorphismProperty (Bounded C) :=
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).inverseImage (ι C)

end

variable [Preadditive C]

noncomputable instance : HasShift (Bounded C) ℤ :=
  (fullyFaithfulι C).hasShift
    (fun (n : ℤ) => ObjectProperty.lift _
    (Bounded.ι C ⋙ CategoryTheory.shiftFunctor (CochainComplex C ℤ) n) (by
      rintro ⟨K, k, hk, l, hl⟩
      exact ⟨k - n, K.isStrictlyLE_shift k n _ (by omega),
        l - n, K.isStrictlyGE_shift l n _ (by omega)⟩))
    (fun n => ObjectProperty.liftCompιIso _ _ _)

instance : (ι C).CommShift ℤ :=
  Functor.CommShift.of_hasShiftOfFullyFaithful _ _ _

end Bounded

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [F.PreservesZeroMorphisms]

def mapCochainComplexBounded : CochainComplex.Bounded C ⥤ CochainComplex.Bounded D :=
  ObjectProperty.lift _ (CochainComplex.Bounded.ι C ⋙ F.mapHomologicalComplex _) (fun K => by
    obtain ⟨i, hi, j, hj⟩ := K.2
    refine ⟨i, ?_, j, ?_⟩
    · dsimp [CochainComplex.Bounded.ι]
      infer_instance
    · dsimp [CochainComplex.Bounded.ι]
      infer_instance)

def mapCochainComplexBoundedCompι :
    F.mapCochainComplexBounded ⋙ CochainComplex.Bounded.ι D ≅
      CochainComplex.Bounded.ι C ⋙ F.mapHomologicalComplex _ := Iso.refl _

end

end Functor

end CategoryTheory
