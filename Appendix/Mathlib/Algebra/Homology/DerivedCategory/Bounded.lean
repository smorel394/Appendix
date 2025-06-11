/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Appendix.Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory
import Appendix.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Appendix.Mathlib.Algebra.Homology.HomotopyCategory.Bounded
import Appendix.Mathlib.Algebra.Homology.DerivedCategory.Basic
import Appendix.Mathlib.CategoryTheory.Triangulated.Subcategory
import Appendix.Mathlib.CategoryTheory.Shift.ShiftSequence

/-!
# D^b

-/

open CategoryTheory Category Triangulated Limits

variable {C : Type*} [Category C] [Abelian C]

namespace HomotopyCategory

namespace Bounded

variable (C)

noncomputable abbrev subcategoryAcyclic :
    Triangulated.Subcategory (HomotopyCategory.Bounded C) :=
  (HomotopyCategory.subcategoryAcyclic C).inverseImage (HomotopyCategory.Bounded.ι C)

lemma quasiIso_eq_subcategoryAcyclic_W :
    HomotopyCategory.Bounded.quasiIso C = (subcategoryAcyclic C).W := by
  ext K L f
  obtain ⟨M, g, h, mem⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle f
  have := (HomotopyCategory.subcategoryAcyclic C).mem_W_iff_of_distinguished _
    ((HomotopyCategory.Bounded.ι C).map_distinguished _ mem)
  erw [← HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W] at this
  erw [(subcategoryAcyclic C).mem_W_iff_of_distinguished _ mem]
  exact this

end Bounded

end HomotopyCategory

namespace DerivedCategory

open TStructure

namespace Bounded

variable [HasDerivedCategory C]

noncomputable def Qh : HomotopyCategory.Bounded C ⥤ Bounded C :=
  t.bounded.lift (HomotopyCategory.Bounded.ι _ ⋙ DerivedCategory.Qh) (by
    rintro ⟨⟨X⟩, n, h, m, h'⟩
    dsimp [bounded, Subcategory.inter]
    refine ⟨?_, ?_⟩
    · exact ⟨m, {ge := (t.ge m).prop_of_iso ((quotientCompQhIso C).symm.app X)
                       (t.ge_of_isGE _ _)}⟩
    · exact ⟨n, {le := (t.le n).prop_of_iso ((quotientCompQhIso C).symm.app X)
                       (t.le_of_isLE _ _)}⟩)

noncomputable instance : (Qh : _ ⥤ Bounded C).CommShift ℤ := by
  dsimp only [Qh]
  infer_instance

instance : (Qh : _ ⥤ Bounded C).IsTriangulated := by
  dsimp only [Qh]
  infer_instance

-- The category of acyclic objects is neither left nor right localizing for the inclusion
-- of the subcategory of bounded objects, but the localization still exists!
-- You have to go through bounded above (or below) objects to get things that are
-- left/right localizing at each step.
/-
instance : (HomotopyCategory.subcategoryAcyclic C).P.IsLeftLocalizing (HomotopyCategory.Bounded.ι C)
    where
  fac {L K} φ hK := by
    obtain ⟨K : CochainComplex C ℤ⟩ := K
    obtain ⟨⟨L : CochainComplex C ℤ⟩, n, (hn : L.IsStrictlyLE n), m, (hm : L.IsStrictlyGE m)⟩ := L
    obtain ⟨φ, rfl⟩ : ∃ (ψ : L ⟶ K), φ = (HomotopyCategory.quotient _ _).map ψ := by
      obtain ⟨ψ⟩ := φ
      exact ⟨ψ, rfl⟩
    let M : HomotopyCategory.Bounded C :=
      ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj ((K.truncLE n).truncGE m), n, by
        change ((K.truncLE n).truncGE _).IsStrictlyLE n
        infer_instance,
        m, by
        change ((K.truncLE n).truncGE _).IsStrictlyGE _
        infer_instance
        ⟩
    have hM : (HomotopyCategory.subcategoryAcyclic C).P ((HomotopyCategory.Bounded.ι C).obj M) := by
      dsimp [M, HomotopyCategory.Bounded.ι]
      rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic,
        (K.truncLE n).acyclic_truncGE_iff (m - 1) m (by omega)]
--        K.acyclic_truncLE_iff n (n + 1) (by omega)]
      erw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
      rw [CochainComplex.isLE_iff]
      intro i _
      by_cases hi : i ≤ n
      · rw [HomologicalComplex.exactAt_iff_isZero_homology]
        have := K.quasiIsoAt_ιTruncLE (ComplexShape.embeddingUpIntLE n) (j' := i)
          (j := (n - i).natAbs)
          (by dsimp; rw [← Int.eq_natAbs_of_nonneg (a := n - i) (by omega)]; omega)
        rw [quasiIsoAt_iff_isIso_homologyMap] at this
        refine Limits.IsZero.of_iso ?_ (asIso (HomologicalComplex.homologyMap
          (HomologicalComplex.ιTruncLE K (ComplexShape.embeddingUpIntLE n)) i))
        rw [← HomologicalComplex.exactAt_iff_isZero_homology]
        exact hK i
      · apply (K.truncLE n).exactAt_of_isSupported (ComplexShape.embeddingUpIntLE n)
        intro
        dsimp
        omega
    have : IsIso (L.ιTruncLE n) := by
      rw [CochainComplex.isIso_ιTruncLE_iff]
      infer_instance
    refine ⟨M, hM, ?_, ?_, ?_⟩

    --(HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (K.ιTruncLE n),
    --  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
    --    (inv (L.ιTruncLE n) ≫ CochainComplex.truncLEMap φ n), ?_⟩
    erw [← (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_comp]
    simp
-/

variable (C)

noncomputable def QhCompιIsoιCompQh :
    Qh ⋙ Bounded.ι ≅ HomotopyCategory.Bounded.ι C ⋙ DerivedCategory.Qh := Iso.refl _

instance : (Qh (C := C)).EssSurj := by sorry
/-  suffices ∀ (X : DerivedCategory C) (n : ℤ) (_ : X.IsGE n),
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE n),
      Nonempty (DerivedCategory.Q.obj K ≅ X) from ⟨by
        rintro ⟨X, ⟨m, hm⟩, ⟨n, hn⟩⟩
        obtain ⟨K, e, h⟩ := hn
        exact ⟨⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K, n, h⟩,
          ⟨Bounded.ι.preimageIso ((quotientCompQhIso C).app _ ≪≫ e.symm)⟩⟩⟩
  intro X n hn
  have : (Q.objPreimage X).IsGE n := by
    rw [← isGE_Q_obj_iff]
    apply t.isGE_of_iso (Q.objObjPreimageIso X).symm
  exact ⟨(Q.objPreimage X).truncGE n, inferInstance,
    ⟨(asIso (Q.map ((Q.objPreimage X).πTruncGE n))).symm ≪≫ Q.objObjPreimageIso X⟩⟩
-/

instance : Qh.IsLocalization (HomotopyCategory.Bounded.subcategoryAcyclic C).W := sorry
/-  (HomotopyCategory.subcategoryAcyclic C).isLocalization_of_isLeftLocalizing
    (HomotopyCategory.Bounded.ι C) (QhCompιIsoιCompQh C)-/

instance : Qh.IsLocalization (HomotopyCategory.Bounded.quasiIso C) := by
  rw [HomotopyCategory.Bounded.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (DerivedCategory.Bounded.ι (C := C)).CommShift ℤ := sorry

instance : (DerivedCategory.Bounded.ι (C := C)).IsTriangulated := sorry

noncomputable def singleFunctors : SingleFunctors C (Bounded C) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors C) Bounded.ι
      (fun n => t.bounded.lift (DerivedCategory.singleFunctor C n)
      (fun _ => sorry/-⟨n, inferInstance⟩-/))
      (fun _ => Iso.refl _)

noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ Bounded C := (singleFunctors C).functor n

noncomputable def singleFunctorιIso (n : ℤ) :
    singleFunctor C n ⋙ Bounded.ι ≅ DerivedCategory.singleFunctor C n := by
  apply SingleFunctors.liftFunctorCompIso

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

noncomputable def homologyFunctor (n : ℤ) : Bounded C ⥤ C :=
    Bounded.ι ⋙ DerivedCategory.homologyFunctor C n

instance (n : ℤ) : (homologyFunctor C n).IsHomological := by
  dsimp [homologyFunctor]
  infer_instance

instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _
    (HomotopyCategory.Bounded.subcategoryAcyclic C).W

variable {C} in
noncomputable def Q : CochainComplex.Bounded C ⥤ Bounded C :=
  t.bounded.lift (CochainComplex.Bounded.ι _ ⋙ DerivedCategory.Q) (by sorry)

noncomputable def QCompιIsoιCompQ :
    Q ⋙ Bounded.ι ≅ CochainComplex.Bounded.ι C ⋙ DerivedCategory.Q := Iso.refl _

noncomputable instance : (Q : _ ⥤ Bounded C).CommShift ℤ := by
  dsimp only [Q]
  infer_instance

instance : (Q (C := C)).EssSurj := by sorry

instance : Q.IsLocalization (CochainComplex.Bounded.quasiIso (C := C)) := by sorry

instance : (CochainComplex.Bounded.quasiIso (C := C)).HasLocalization := sorry

instance : (Q (C := C)).mapArrow.EssSurj := sorry

/-- The natural isomorphism `HomotopyCategory.Bounded.quotient C ⋙ Qh ≅ Q`. -/
def quotientCompQhIso : HomotopyCategory.Bounded.quotient C ⋙ Qh ≅ Q := sorry
--  HomologicalComplexUpToQuasiIso.quotientCompQhIso C (ComplexShape.up ℤ)

variable {C}

noncomputable abbrev TStructure.t : TStructure (DerivedCategory.Bounded C) :=
  (DerivedCategory.TStructure.t (C := C)).bounded.tStructure DerivedCategory.TStructure.t

abbrev IsGE (X : Bounded C) (n : ℤ) : Prop := Bounded.TStructure.t.IsGE X n
abbrev IsLE (X : Bounded C) (n : ℤ) : Prop := Bounded.TStructure.t.IsLE X n

lemma isGE_ι_obj_iff (X : DerivedCategory.Bounded C) (n : ℤ) :
    (ι.obj X).IsGE n ↔ X.IsGE n := by
  constructor
  all_goals exact fun h => ⟨h.1⟩

lemma isLE_ι_obj_iff (X : DerivedCategory.Bounded C) (n : ℤ) :
    (ι.obj X).IsLE n ↔ X.IsLE n := by
  constructor
  all_goals exact fun h => ⟨h.1⟩

instance (X : Bounded C) (n : ℤ) [X.IsGE n] : (ι.obj X).IsGE n := by
  rw [isGE_ι_obj_iff]
  infer_instance

instance (X : Bounded C) (n : ℤ) [X.IsLE n] : (ι.obj X).IsLE n := by
  rw [isLE_ι_obj_iff]
  infer_instance

noncomputable instance : (DerivedCategory.Bounded.homologyFunctor C 0).ShiftSequence ℤ := by
  dsimp [homologyFunctor]
  exact Functor.ShiftSequence.comp_left _ _ _

instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).IsGE n := by
  rw [← isGE_ι_obj_iff]
  change DerivedCategory.TStructure.t.IsGE ((DerivedCategory.singleFunctor C n).obj X) n
  infer_instance

instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).IsLE n := by
  rw [← isLE_ι_obj_iff]
  change DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor C n).obj X) n
  infer_instance

lemma isZero_homology_of_isGE
    (X : DerivedCategory.Bounded C) (n : ℤ) [X.IsGE n] (i : ℤ) (hi : i < n) :
    IsZero ((homologyFunctor C i).obj X) :=
  (ι.obj X).isZero_of_isGE n i hi

lemma isZero_homology_of_isLE
    (X : DerivedCategory.Bounded C) (n : ℤ) [X.IsLE n] (i : ℤ) (hi : n < i) :
    IsZero ((homologyFunctor C i).obj X) :=
  (ι.obj X).isZero_of_isLE n i hi

lemma isIso_iff {X Y : DerivedCategory.Bounded C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ (n : ℤ), IsIso ((homologyFunctor C n).map f) := by
  constructor
  · intro _ n
    infer_instance
  · intro h
    have : IsIso (ι.map f) := by
      rw [DerivedCategory.isIso_iff]
      exact h
    apply isIso_of_fully_faithful ι

end Bounded

end DerivedCategory
