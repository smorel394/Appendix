/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Appendix.Mathlib.CategoryTheory.Shift.SingleFunctorsLift
import Appendix.Mathlib.Algebra.Homology.CochainComplexBounded
import Appendix.Mathlib.CategoryTheory.Triangulated.Subcategory
import Appendix.Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Appendix.Mathlib.Algebra.Homology.HomotopyCategory
import Appendix.Mathlib.Algebra.Homology.DerivedCategory.Basic
import Appendix.Mathlib.CategoryTheory.Shift.Quotient

/-!
# K^b

-/

open CategoryTheory Category Limits Triangulated ZeroObject Pretriangulated

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {D : Type _} [Category D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  (A : Type _) [Category A] [Abelian A]

namespace HomotopyCategory

def bounded : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  fun K ↦ ∃ (n : ℤ), CochainComplex.IsStrictlyLE K.1 n ∧
          ∃ (m : ℤ), CochainComplex.IsStrictlyGE K.1 m

instance : (bounded C).IsTriangulated where
  exists_zero := by
    refine ⟨⟨0⟩, ?_, ⟨0, ?_, 0, ?_⟩⟩
    · change IsZero ((quotient _ _).obj 0)
      rw [IsZero.iff_id_eq_zero, ← (quotient _ _).map_id, id_zero, Functor.map_zero]
    · dsimp
      infer_instance
    · dsimp
      infer_instance
  isStableUnderShiftBy n :=
    { le_shift := by
        rintro ⟨X : CochainComplex C ℤ⟩ ⟨k, _ : X.IsStrictlyLE k, l, _ : X.IsStrictlyGE l⟩
        refine ⟨k - n, ?_, l - n, ?_⟩
        · erw [Quotient.functor_obj_shift]
          exact X.isStrictlyLE_shift k n (k - n) (by omega)
        · erw [Quotient.functor_obj_shift]
          exact X.isStrictlyGE_shift l n (l - n) (by omega)}
  ext₂' T hT := by
    rintro ⟨n₁, _, m₁, _⟩ ⟨n₃, _, m₃, _⟩
    obtain ⟨f : T.obj₃.as ⟶ T.obj₁.as⟦(1 : ℤ)⟧, hf⟩ := (quotient _ _ ).map_surjective
      (T.mor₃ ≫ ((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app T.obj₁.as)
    let T₁ := T.rotate.rotate
    have hT₁ : T₁ ∈ distTriang _ := rot_of_distTriang _ (rot_of_distTriang _ hT)
    let T₂ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
      (CochainComplex.mappingCone.triangle f)
    have hT₂ : T₂ ∈ distTriang _ := by exact ⟨_, _, f, ⟨Iso.refl _⟩⟩
    have e := isoTriangleOfIso₁₂ T₁ T₂ hT₁ hT₂ (Iso.refl _)
      (((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).symm.app T.obj₁.as)
      (by dsimp [T₁, T₂]; rw [id_comp, hf])
    refine ⟨(quotient C (ComplexShape.up ℤ)).obj ((shiftFunctor (CochainComplex C ℤ) (-1)).obj
      (CochainComplex.mappingCone f)), ?_, ⟨?_⟩⟩
    · refine ⟨max n₁ n₃, ?_, min m₁ m₃, ?_⟩
      · let n₀ : ℤ := max n₁ n₃ - 1
        have := le_max_left n₁ n₃
        have := le_max_right n₁ n₃
        have : CochainComplex.IsStrictlyLE (CochainComplex.mappingCone f) n₀ := by
          rw [CochainComplex.isStrictlyLE_iff]
          intro i hi
          simp only [CochainComplex.mappingCone.isZero_X_iff]
          constructor
          · exact CochainComplex.isZero_of_isStrictlyLE T.obj₃.as n₃ (i + 1) (by omega)
          · exact CochainComplex.isZero_of_isStrictlyLE T.obj₁.as n₁ (i + 1) (by omega)
        have := CochainComplex.isStrictlyLE_shift (CochainComplex.mappingCone f) n₀ (-1)
          (n₀ + 1) (by omega)
        simp only [Int.reduceNeg, sub_add_cancel, n₀] at this
        exact this
      · let n₀ : ℤ := min m₁ m₃ - 1
        have := min_le_left m₁ m₃
        have := min_le_right m₁ m₃
        have : CochainComplex.IsStrictlyGE (CochainComplex.mappingCone f) n₀ := by
          rw [CochainComplex.isStrictlyGE_iff]
          intro i hi
          simp only [CochainComplex.mappingCone.isZero_X_iff]
          constructor
          · exact CochainComplex.isZero_of_isStrictlyGE T.obj₃.as m₃ (i + 1) (by omega)
          · exact CochainComplex.isZero_of_isStrictlyGE T.obj₁.as m₁ (i + 1) (by omega)
        have := CochainComplex.isStrictlyGE_shift (CochainComplex.mappingCone f) n₀ (-1)
          (n₀ + 1) (by omega)
        simp only [Int.reduceNeg, sub_add_cancel, n₀] at this
        exact this
    · exact (shiftEquiv _ (1 : ℤ)).unitIso.app T.obj₂ ≪≫
        (shiftFunctor _ (-1)).mapIso (Triangle.π₃.mapIso e) ≪≫
        ((quotient _ _).commShiftIso (-1)).symm.app (CochainComplex.mappingCone f)

abbrev Bounded := (bounded C).FullSubcategory

namespace Bounded

abbrev ι : Bounded C ⥤ HomotopyCategory C (ComplexShape.up ℤ) := (bounded C).ι

def quasiIso : MorphismProperty (Bounded A) := (HomotopyCategory.quasiIso A _).inverseImage (ι A)

instance : (quasiIso A).IsMultiplicative := by
  dsimp only [quasiIso]
  infer_instance

instance : (quasiIso A).IsCompatibleWithShift ℤ where
  condition a := by
    ext X Y f
    refine Iff.trans ?_ (MorphismProperty.IsCompatibleWithShift.iff
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ((ι A).map f) a)
    exact (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoOfNatIso ((ι A).commShiftIso a) (Arrow.mk f))

def quotient : CochainComplex.Bounded C ⥤ Bounded C :=
  ObjectProperty.lift _
    (CochainComplex.Bounded.ι C ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ)) (by
      rintro ⟨K, n, hn⟩
      exact ⟨n, hn⟩)

instance : (HomotopyCategory.Bounded.quotient C).IsLocalization
    (CochainComplex.Bounded.homotopyEquivalences C) := sorry

def quotientCompι :
  quotient C ⋙ ι C ≅
    CochainComplex.Bounded.ι C ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ) := by
  apply ObjectProperty.liftCompιIso

noncomputable def singleFunctors : SingleFunctors C (Bounded C) ℤ :=
  SingleFunctors.lift (HomotopyCategory.singleFunctors C) (ι C)
    (fun n => (bounded C).lift (singleFunctor C n) (fun X => by
      refine ⟨n, ?_, n, ?_⟩
      · change ((CochainComplex.singleFunctor C n).obj X).IsStrictlyLE n
        infer_instance
      · change ((CochainComplex.singleFunctor C n).obj X).IsStrictlyGE n
        infer_instance))
    (fun n => Iso.refl _)

noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ Bounded C := (singleFunctors C).functor n

noncomputable def singleFunctorιIso (n : ℤ) :
    singleFunctor C n ⋙ ι C ≅ HomotopyCategory.singleFunctor C n := by
  apply SingleFunctors.liftFunctorCompIso

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

end Bounded

end HomotopyCategory

namespace CategoryTheory

namespace Functor

variable {C}
variable (F : C ⥤ D) [F.Additive]

def mapHomotopyCategoryBounded : HomotopyCategory.Bounded C ⥤ HomotopyCategory.Bounded D :=
  (HomotopyCategory.bounded D).lift
    (HomotopyCategory.Bounded.ι C ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ)) (by
      rintro ⟨X, ⟨n, _,m, _⟩⟩
      refine ⟨n, ?_, m, ?_⟩
      · dsimp [HomotopyCategory.Bounded.ι, HomotopyCategory.quotient, Quotient.functor]
        infer_instance
      · dsimp [HomotopyCategory.Bounded.ι, HomotopyCategory.quotient, Quotient.functor]
        infer_instance)

noncomputable instance : (F.mapHomotopyCategoryBounded).CommShift ℤ := by
  dsimp only [mapHomotopyCategoryBounded]
  infer_instance

instance : (F.mapHomotopyCategoryBounded).IsTriangulated := by
  dsimp only [mapHomotopyCategoryBounded]
  infer_instance

noncomputable instance [Full F] [Faithful F] : Full F.mapHomotopyCategoryBounded where
  map_surjective f := ⟨(F.mapHomotopyCategory _).preimage f,
    (F.mapHomotopyCategory _).map_preimage f⟩

noncomputable instance [Full F] [Faithful F] : Faithful F.mapHomotopyCategoryBounded where
  map_injective h := (F.mapHomotopyCategory _).map_injective h

def mapHomotopyCategoryBoundedCompIso {E : Type*} [Category E] [Preadditive E] [HasZeroObject E]
    [HasBinaryBiproducts E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] :
    H.mapHomotopyCategoryBounded ≅ F.mapHomotopyCategoryBounded ⋙ G.mapHomotopyCategoryBounded :=
  ((HomotopyCategory.bounded _).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (HomotopyCategory.Bounded.ι C)
      (mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)))

/-- The obvious isomorphism between
`HomotopyCategory.Bounded.quotient C ⋙ F.mapHomotopyCategoryBounded` and
`F.mapCochainComplexBounded ⋙ HomotopyCategory.Bounded.quotient D` when `F : C ⥤ D` is
an additive functor. -/
def mapHomotopyCategoryBoundedFactors (F : C ⥤ D) [F.Additive] :
    HomotopyCategory.Bounded.quotient C ⋙ F.mapHomotopyCategoryBounded ≅
      F.mapCochainComplexBounded ⋙ HomotopyCategory.Bounded.quotient D := sorry
--  CategoryTheory.Quotient.lift.isLift _ _ _

end Functor

end CategoryTheory
