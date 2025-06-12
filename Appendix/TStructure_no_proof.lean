import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Appendix.Mathlib.Algebra.Homology.DerivedCategory.Bounded
import Appendix.Mathlib.CategoryTheory.Triangulated.TStructure.Homology
import Appendix.Mathlib.CategoryTheory.Triangulated.TStructure.TExact
import Appendix.Filtered_no_proof

noncomputable section

open CategoryTheory Preadditive Limits Triangulated CategoryTheory.FilteredTriangulated Category

open scoped ZeroObject

namespace CategoryTheory

universe u v u₁ v₁ u₂ v₂ u₃ v₃

attribute [local instance] endofunctorMonoidalCategory

variable {C : Type u} [Category.{v, u} C] [HasShift C (ℤ × ℤ)] [Preadditive C] [HasZeroObject C]
  [∀ p : ℤ × ℤ, Functor.Additive (shiftFunctor C p)] [Pretriangulated C] [FilteredTriangulated C]
  [IsTriangulated C]

variable {A : Type u₁} [Category.{v₁} A] [HasShift A ℤ] [Preadditive A] [HasZeroObject A]
  [∀ p : ℤ, Functor.Additive (shiftFunctor A p)] [Pretriangulated A]
  [IsTriangulated A]

variable (L : isFilteredTriangulated_over C A) (t : TStructure A)

local instance : L.functor.CommShift ℤ := L.commShift

local instance : L.functor.IsTriangulated := L.triangulated

namespace Triangulated.TStructure

-- Definition A.2.1
class IsCompatible (tF : TStructure C) where
  exact_functor : L.functor.TExact t tF
  compat_shift (a b n : ℤ) (h : b + n = a) (X : C) (hX : TStructure.IsLE tF X a) :
      TStructure.IsLE tF ((shiftFunctor₂ C n).obj X) b
-- Here we reformulate the compatibility with shifts to make it easier to use.

-- Proposition A.2.2:
-- Construction of a compatible t-structure on `C` given a t-structure on `A`.
-- Note the ambiguity (we don't know whether the shift applies before or after `Gr`). It doesn't
-- matter because `Gr` commutes with shifts, but in Lean we need to make a choice.
def compatible : TStructure C where
  le n X := ∀ (i : ℤ), TStructure.IsLE t (((Gr L i).obj X)⟦i⟧) n
  ge n X := ∀ (i : ℤ), TStructure.IsGE t (((Gr L i).obj X)⟦i⟧) n
  le_isClosedUnderIsomorphisms n :=
    {of_iso {X Y} e h i := {le := (t.le n).prop_of_iso ((shiftFunctor A i).mapIso
                                  ((Gr L i).mapIso e)) (t.le_of_isLE _ _)}}
  ge_isClosedUnderIsomorphisms n :=
    {of_iso {X Y} e h i := {ge := (t.ge n).prop_of_iso ((shiftFunctor A i).mapIso
                                  ((Gr L i).mapIso e)) (t.ge_of_isGE _ _)}}
  le_shift n a n' h X hX i := by
    have : t.IsLE ((shiftFunctor A a).obj ((shiftFunctor A i).obj ((Gr L i).obj X))) n' := by
      refine {le := ?_}
      change (t.le _).shift _ _
      rw [t.shift_le _ _ _ h]
      exact t.le_of_isLE _ _
    exact {le := (t.le n').prop_of_iso ((shiftFunctor A i).mapIso (((Gr L i).commShiftIso a).app X)
      ≪≫ shiftComm _ a i).symm (t.le_of_isLE _ _)}
  ge_shift n a n' h X hX i := by
    have : t.IsGE ((shiftFunctor A a).obj ((shiftFunctor A i).obj ((Gr L i).obj X))) n' := by
      refine {ge := ?_}
      change (t.ge _).shift _ _
      rw [t.shift_ge _ _ _ h]
      exact t.ge_of_isGE _ _
    exact {ge := (t.ge n').prop_of_iso ((shiftFunctor A i).mapIso (((Gr L i).commShiftIso a).app X)
      ≪≫ shiftComm _ a i).symm (t.ge_of_isGE _ _)}
  zero' X Y f hX hY := by
    sorry -- this one actually takes nontrivial work (the fact that each object of `C` is
          -- a successive extension of its graded pieces)
  le_zero_le X hX i := {le := t.le_monotone zero_le_one _ (t.le_of_isLE _ _)}
  ge_one_le X hX i := {ge := t.ge_antitone zero_le_one _ (t.ge_of_isGE _ _)}
  exists_triangle_zero_one := sorry
-- This one also takes a bit of work! (Induction on the length of the filtration, but the
-- induction step will use the uniqueness of the triangle.)

-- Proposition A.2.2:
-- Compatibility of the constructed t-structure on `C`.
instance compatible_is_compatible : t.IsCompatible L (t.compatible L) where
  exact_functor := by
    refine {rightTExact := {objGE := fun X n _ ↦ {ge i := ?_}},
            leftTExact := {objLE := fun X n _ ↦ {le i := ?_}}}
    · by_cases h : i = 0
      · have : t.IsGE (((𝟭 A).obj X)⟦i⟧) n := by
          have : t.IsGE ((𝟭 A).obj X) n := by dsimp; infer_instance
          exact {ge := (t.ge n).prop_of_iso ((shiftFunctorZero' A i h).app X).symm
                       (t.ge_of_isGE _ _)}
        exact {ge := (t.ge n).prop_of_iso ((shiftFunctor A i).mapIso
                     ((Gr_pure_of_zero L i h).app X)).symm (t.ge_of_isGE _ _)}
      · exact t.isGE_of_isZero _ (Functor.map_isZero (shiftFunctor A i)
          (Gr_pure_zero_of_ne_zero L h X)) n
    · by_cases h : i = 0
      · have : t.IsLE (((𝟭 A).obj X)⟦i⟧) n := by
          have : t.IsLE ((𝟭 A).obj X) n := by dsimp; infer_instance
          exact {le := (t.le n).prop_of_iso ((shiftFunctorZero' A i h).app X).symm
                       (t.le_of_isLE _ _)}
        exact {le := (t.le n).prop_of_iso ((shiftFunctor A i).mapIso
                     ((Gr_pure_of_zero L i h).app X)).symm (t.le_of_isLE _ _)}
      · exact t.isLE_of_isZero _ (Functor.map_isZero (shiftFunctor A i)
          (Gr_pure_zero_of_ne_zero L h X)) n
  compat_shift a b n h X hX := by
    refine {le := fun i ↦ ?_}
    dsimp [compatible] at hX ⊢
    have := hX.le (i - n)
    have : t.IsLE ((shiftFunctor A (i - n) ⋙ shiftFunctor A n).obj ((Gr L (i - n)).obj X)) b := by
      refine {le := ?_}
      change (t.le _).shift _ _
      rw [t.shift_le _ _ a (by omega)]
      exact t.le_of_isLE _ _
    exact {le := (t.le b).prop_of_iso ((shiftFunctor A i).mapIso (((Gr_commShift L).iso i n (i - n)
                 (by simp)).app X) ≪≫ (shiftFunctorAdd' A (i - n) n i (by simp)).app _).symm
                 (t.le_of_isLE _ _)}

-- Proposition A.2.2:
-- Uniqueness of the compatible t-structure.
lemma compatible_uniq (tF : TStructure C) [t.IsCompatible L tF] : tF = t.compatible L := sorry

section Realization

-- Theorem A.2.3
-- First we need to construct the functor `H_F : C → CochainComplex t.Heart ℤ`.
-- In the paper, the `n`th degree of `H_F X` is defined as
-- `(t.homology n).obj ((Gr L n).obj X)`. Given the new definition of `Gr`, we can rewrite
-- this as `(t.homology n).obj ((ForgetFiltration L).obj ((truncGELE n n).obj X))`, which
-- is useful to construct the differentials.

variable (tF : TStructure C)

local instance : t.HasHeart := hasHeartFullSubcategory t

local instance : tF.HasHeart := hasHeartFullSubcategory tF

noncomputable local instance : t.HasHomology₀ := t.hasHomology₀
noncomputable local instance : tF.HasHomology₀ := tF.hasHomology₀

noncomputable local instance : t.homology₀.ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

noncomputable local instance : tF.homology₀.ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

/-!
Characterization of the heart of the t-structure on `C`.
-/

lemma mem_filtered_heart_iff (X : C) :
    tF.heart X ↔ ∀ (n : ℤ), t.heart (((Gr L n).obj X)⟦n⟧) := sorry

-- Theorem A.2.3(i):
-- The functor is well-defined.
@[simp]
def FilteredToComplex_deg (n : ℤ) : C ⥤ t.Heart :=
  Gr L n ⋙ t.homology n

@[simp]
def FilteredToComplex_deg_aux (n : ℤ) : C ⥤ C :=
  FilteredTriangulated.truncGELE n n ⋙ shiftFunctor C n

def FilteredToComplex_diff (n : ℤ) :
    FilteredToComplex_deg L t n ⟶ FilteredToComplex_deg L t (n + 1) where
  app X := t.homologyδ ((ForgetFiltration L).mapTriangle.obj ((truncGELE_triangle n n (n + 1)
    (le_refl _) (by simp)).obj X)) n (n + 1) rfl
  naturality f := sorry

def FilteredToComplex_diff_aux (n : ℤ) :
    FilteredToComplex_deg_aux (C := C) n ⟶ FilteredToComplex_deg_aux (n + 1) where
  app X := ((truncGELE_δ n n (n + 1)).app X)⟦n⟧' ≫
    (shiftFunctorAdd' C 1 n (n + 1) (add_comm _ _)).inv.app _
  naturality X Y f := by
    dsimp
    slice_lhs 1 2 => rw [← Functor.map_comp, (truncGELE_δ n n (n + 1)).naturality, Functor.map_comp]
    rw [Functor.comp_map, ← Functor.comp_map (shiftFunctor C 1) (shiftFunctor C n), assoc,
      (shiftFunctorAdd' C 1 n (n + 1) (add_comm _ _)).inv.naturality]
    simp only [Functor.comp_obj, assoc]

@[simp]
def FilteredToComplex_deg_comp_ι (n : ℤ) :
    tF.ιHeart ⋙ FilteredToComplex_deg L t n ⋙ t.ιHeart ⋙ L.functor ≅
    tF.ιHeart ⋙ FilteredToComplex_deg_aux n := by
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine (t.homology n ⋙ t.ιHeart ⋙ L.functor).mapIso
      ((shiftEquiv A n).unitIso.app ((Gr L n).obj (tF.ιHeart.obj X))) ≪≫ ?_
    refine (t.ιHeart ⋙ L.functor).mapIso ((t.homology₀.shiftIso (-n) n 0 (neg_add_cancel _)).app
      ((shiftFunctor A n).obj ((Gr L n).obj (tF.ιHeart.obj X)))) ≪≫ ?_
    have prop : t.heart (((Gr L n).obj (tF.ιHeart.obj X))⟦n⟧) := sorry
    set e : ((Gr L n).obj (tF.ιHeart.obj X))⟦n⟧ ≅
      t.ιHeart.obj ⟨((Gr L n).obj (tF.ιHeart.obj X))⟦n⟧, prop⟩ := Iso.refl _
    refine (t.homology₀.shift 0 ⋙ t.ιHeart ⋙ L.functor).mapIso e ≪≫ ?_
    refine (t.ιHeart ⋙ L.functor).mapIso (t.ιHeartHomology_zero.app
      ⟨((Gr L n).obj (tF.ιHeart.obj X))⟦n⟧, prop⟩) ≪≫ ?_
    refine L.functor.mapIso e.symm ≪≫ ?_
    refine L.functor.mapIso (((ForgetFiltration L).commShiftIso n).symm.app
      ((FilteredTriangulated.truncGELE n n).obj (tF.ιHeart.obj X))) ≪≫ ?_
    refine (Functor_forgetFiltration L).app ((shiftFunctor C n).obj
      ((FilteredTriangulated.truncGELE n n).obj (tF.ιHeart.obj X))) ≪≫ ?_
    have : FilteredTriangulated.IsLE ((shiftFunctor C n).obj
      ((FilteredTriangulated.truncGELE n n).obj (tF.ιHeart.obj X))) 0 := sorry
    refine (FilteredTriangulated.truncGE 0).mapIso (asIso ((truncLEπ 0).app ((shiftFunctor C n).obj
      ((FilteredTriangulated.truncGELE n n).obj (tF.ιHeart.obj X))))).symm ≪≫ ?_
    have : FilteredTriangulated.IsGE ((shiftFunctor C n).obj
      ((FilteredTriangulated.truncGELE n n).obj (tF.ιHeart.obj X))) 0 := sorry
    exact asIso ((truncGEι 0).app ((shiftFunctor C n).obj
      ((FilteredTriangulated.truncGELE n n).obj (tF.ιHeart.obj X))))
  · intro X Y f
    dsimp
    simp only [Functor.map_id, Functor.map_inv, id_comp, assoc]
    sorry

lemma FilteredToComplex_diff_comp_ι (n : ℤ) (X : tF.Heart) :
    (FilteredToComplex_deg_comp_ι L t tF n).hom.app X ≫
    (FilteredToComplex_diff_aux n).app (tF.ιHeart.obj X) =
    L.functor.map (t.ιHeart.map ((FilteredToComplex_diff L t n).app (tF.ιHeart.obj X))) ≫
    (FilteredToComplex_deg_comp_ι L t tF (n + 1)).hom.app X := by
  dsimp
  simp only [Functor.map_id, Functor.map_inv, id_comp, assoc]
  sorry

variable (X : C) (n : ℤ)

example : (FilteredTriangulated.truncGELE n n ⋙ shiftFunctor C n).obj X ⟶
    (FilteredTriangulated.truncGELE (n + 1) (n + 1) ⋙ shiftFunctor C (n + 1)).obj X :=
  ((truncGELE_δ n n (n + 1)).app X)⟦n⟧' ≫ (shiftFunctorAdd' C 1 n (n + 1) (add_comm _ _)).inv.app _

lemma FilteredToComplex_deg_comp_ι_diff (n : ℤ) (X : tF.Heart) :
    (FilteredToComplex_deg_comp_ι L t tF n).hom.app X ≫ sorry
    = L.functor.map (t.ιHeart.map ((FilteredToComplex_diff L t n).app (tF.ιHeart.obj X))) ≫
      (FilteredToComplex_deg_comp_ι L t tF (n + 1)).hom.app X := sorry

def FilteredToComplex_condition (n : ℤ) :
    FilteredToComplex_diff L t n ≫ FilteredToComplex_diff L t (n + 1) = 0 := by
-- We don't need the triangle to be distinguished to define the connecting
-- morphism, but we will need it to check that the differentials
-- compose to 0.
  ext X
  have := (ForgetFiltration L).map_distinguished _ (truncGELE_triangle_distinguished
      n n (n + 1) (le_refl _) (by simp) X)
  sorry

def FilteredToComplexObj : CochainComplex (C ⥤ t.Heart) ℤ :=
  CochainComplex.of (FilteredToComplex_deg L t)
    (FilteredToComplex_diff L t) (FilteredToComplex_condition L t)

def FilteredToComplex : C ⥤ CochainComplex t.Heart ℤ := (FilteredToComplexObj L t).asFunctor

omit [IsTriangulated C] in
lemma FilteredToComplex_isBounded (X : C) :
    CochainComplex.bounded t.Heart ((FilteredToComplex L t).obj X) := by
  dsimp [CochainComplex.bounded]
  obtain ⟨n, hn⟩ := Gr_bounded_above L X
  obtain ⟨m, hm⟩ := Gr_bounded_below L X
  refine ⟨n, ?_, m, ?_⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i h
    refine (t.homology i).map_isZero ?_
    exact hn i h
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i h
    refine (t.homology i).map_isZero ?_
    exact hm i h

def FilteredToBoundedComplex : C ⥤ CochainComplex.Bounded t.Heart :=
  (CochainComplex.bounded t.Heart).lift (FilteredToComplex L t)
  (FilteredToComplex_isBounded L t)

-- Theorem A.2.3(i):
-- The restriction of `FilteredToComplex` to the heart of `tF` is
-- an equivalence.
instance FilteredToBoundedComplex_equivalence [t.IsCompatible L tF] :
    (tF.ιHeart ⋙ FilteredToBoundedComplex L t).IsEquivalence := sorry

variable [t.IsCompatible L tF]

-- Theorem A.2.3(i):
-- Indentification of the cohomology functor of `tF`. Again we have
-- an "equality" statement that is actually an "existence of isomorphism"
-- statement, and again the properties of that isomorphism are not clear
-- from the statement.
def HomologyFunctor_iso :
    FilteredToBoundedComplex L t ⋙ (tF.ιHeart ⋙ FilteredToBoundedComplex L t).inv ≅
    tF.homology 0 := sorry

-- Theorem A.2.3(ii):
-- We want the functor to send quasi-isomorphisms to isomorphisms.
lemma Realization_aux :
    (CochainComplex.Bounded.quasiIso (C := t.Heart)).IsInvertedBy
    ((tF.ιHeart ⋙ FilteredToBoundedComplex L t).inv ⋙ tF.ιHeart ⋙
    (ForgetFiltration L)) := sorry

local instance : HasDerivedCategory t.Heart :=
  HasDerivedCategory.standard t.Heart

-- Definition A.2.4:
def Realization : DerivedCategory.Bounded t.Heart ⥤ A :=
  Localization.lift ((tF.ιHeart ⋙ FilteredToBoundedComplex L t).inv ⋙ tF.ιHeart ⋙
    (ForgetFiltration L)) (Realization_aux L t tF)
    DerivedCategory.Bounded.Q

def Realization_comp_Q :
    (tF.ιHeart ⋙ FilteredToBoundedComplex L t) ⋙ DerivedCategory.Bounded.Q ⋙ Realization L t tF
    ≅ tF.ιHeart ⋙ ForgetFiltration L := by
  dsimp [Realization]
  exact isoWhiskerLeft _ (Localization.Lifting.iso _ (CochainComplex.Bounded.quasiIso (C := t.Heart))
    ((tF.ιHeart ⋙ FilteredToBoundedComplex L t).inv ⋙ tF.ιHeart ⋙
    (ForgetFiltration L)) _) ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight
    (tF.ιHeart ⋙ FilteredToBoundedComplex L t).asEquivalence.unitIso.symm _ ≪≫
    (Functor.rightUnitor _).symm

end Realization

end Triangulated.TStructure

end CategoryTheory
