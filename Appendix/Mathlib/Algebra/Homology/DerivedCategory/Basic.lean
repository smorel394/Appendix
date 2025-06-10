/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # The derived category of an abelian category

Addendum to the mathlib file.

-/

assert_not_exists TwoSidedIdeal

universe w v u

open CategoryTheory Category Limits Pretriangulated ZeroObject

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace HomotopyCategory

variable {C}

lemma quotient_obj_mem_subcategoryAcyclic_iff_acyclic (K : CochainComplex C ℤ) :
    (subcategoryAcyclic C).P ((quotient _ _).obj K) ↔ K.Acyclic := by
  apply quotient_obj_mem_subcategoryAcyclic_iff_exactAt

variable (C)

instance : (quasiIso C (ComplexShape.up ℤ)).IsCompatibleWithShift ℤ := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance quasiIso_respectsIso : (quasiIso C (ComplexShape.up ℤ)).RespectsIso := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

end HomotopyCategory

variable [HasDerivedCategory.{w} C]

namespace DerivedCategory

instance : Qh.IsLocalization (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp [Qh, DerivedCategory]
  infer_instance

instance : Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic C).W := by
  rw [← HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

noncomputable instance : Preadditive (DerivedCategory C) :=
  Localization.preadditive Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Qh (C := C)).Additive :=
  Localization.functor_additive Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Q (C := C)).Additive :=
  Functor.additive_of_iso (quotientCompQhIso C)

noncomputable instance : HasZeroObject (DerivedCategory C) :=
  Q.hasZeroObject_of_additive

noncomputable instance : HasShift (DerivedCategory C) ℤ :=
  HasShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).W ℤ

noncomputable instance : (Qh (C := C)).CommShift ℤ :=
  Functor.CommShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).W ℤ

noncomputable instance : (Q (C := C)).CommShift ℤ :=
  Functor.CommShift.ofIso (quotientCompQhIso C) ℤ

instance : NatTrans.CommShift (quotientCompQhIso C).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (quotientCompQhIso C) ℤ

instance shiftFunctor_additive (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Additive := by
  rw [Localization.functor_additive_iff
    Qh (HomotopyCategory.subcategoryAcyclic C).W]
  exact Functor.additive_of_iso (Qh.commShiftIso n)

noncomputable instance : Pretriangulated (DerivedCategory C) :=
  Triangulated.Localization.pretriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Qh (C := C)).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor
    Qh (HomotopyCategory.subcategoryAcyclic C).W

noncomputable instance : IsTriangulated (DerivedCategory C) :=
  Triangulated.Localization.isTriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).W

noncomputable instance (n : ℤ) :
  Localization.Lifting Qh (HomotopyCategory.subcategoryAcyclic C).W
    (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n ⋙ Qh)
    (shiftFunctor (DerivedCategory C) n) := ⟨(Qh.commShiftIso n).symm⟩

instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _ (HomotopyCategory.subcategoryAcyclic C).W

instance {D : Type*} [Category D] : ((whiskeringLeft _ _ D).obj (Qh (C := C))).Full :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Full

instance {D : Type*} [Category D] : ((whiskeringLeft _ _ D).obj (Qh (C := C))).Faithful :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Faithful

instance : (Q : _ ⥤ DerivedCategory C).mapArrow.EssSurj where
  mem_essImage φ := by
    obtain ⟨⟨K⟩, ⟨L⟩, f, ⟨e⟩⟩ :
        ∃ (K L : HomotopyCategory C (ComplexShape.up ℤ)) (f : K ⟶ L),
          Nonempty (Arrow.mk (Qh.map f) ≅ φ) := ⟨_, _, _, ⟨Qh.mapArrow.objObjPreimageIso φ⟩⟩
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective f
    exact ⟨Arrow.mk f, ⟨e⟩⟩

instance : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).HasLeftCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).HasRightCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (Qh : _ ⥤ DerivedCategory C).EssSurj :=
  Localization.essSurj _ (HomotopyCategory.quasiIso _ _)

instance : (Q : _ ⥤ DerivedCategory C).EssSurj :=
  Localization.essSurj _ (HomologicalComplex.quasiIso _ _)

lemma induction_Q_obj (P : DerivedCategory C → Prop)
    (hP₁ : ∀ (X : CochainComplex C ℤ), P (Q.obj X))
    (hP₂ : ∀ ⦃X Y : DerivedCategory C⦄ (_ : X ≅ Y), P X → P Y)
    (X : DerivedCategory C) : P X :=
  hP₂ (Q.objObjPreimageIso X) (hP₁ _)

/-- The isomorphism `singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ Q`. -/
noncomputable def singleFunctorIsoCompQ (n : ℤ) :
    singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ Q := Iso.refl _

end DerivedCategory
