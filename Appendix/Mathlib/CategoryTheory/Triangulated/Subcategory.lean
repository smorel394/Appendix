/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Appendix.Mathlib.CategoryTheory.Shift.CommShift
import Appendix.Mathlib.CategoryTheory.Triangulated.Functor
import Appendix.Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Triangulated subcategories

Addendum to the mathlib file.

-/

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

namespace Limits

variable {C J₁ J₂ : Type _} [Category C]
  (X : J₂ → C) (e : J₁ ≃ J₂) [HasProduct X]

noncomputable def fanOfEquiv : Fan (X ∘ e) := Fan.mk (∏ᶜ X) (fun _ => Pi.π _ _)

@[simp]
lemma fanOfEquiv_proj (j : J₁) : (fanOfEquiv X e).proj j = Pi.π _ (e j) := rfl

@[reassoc]
lemma Fan.congr_proj {J : Type _} {F : J → C} (s : Fan F)
    {j₁ j₂ : J} (h : j₁ = j₂) : s.proj j₁ ≫ eqToHom (by rw [h]) = s.proj j₂ := by
  subst h
  simp

@[reassoc]
lemma Pi.congr_π {J : Type _} (F : J → C) [HasProduct F] {j₁ j₂ : J} (h : j₁ = j₂) :
    Pi.π F j₁ ≫ eqToHom (by rw [h]) = Pi.π F j₂ := by
  subst h
  simp

noncomputable def isLimitFanOfEquiv : IsLimit (fanOfEquiv X e) :=
  mkFanLimit _ (fun s => Pi.lift (fun j₂ => s.proj (e.symm j₂) ≫ eqToHom (by simp) ))
    (fun s j => by simp [Fan.congr_proj _ (e.symm_apply_apply j)])
    (fun s m hm => Limits.Pi.hom_ext (f := X) _ _ (fun j ↦ by simp [← hm]))

lemma hasProductOfEquiv : HasProduct (X ∘ e) :=
  ⟨⟨_, isLimitFanOfEquiv X e⟩⟩

noncomputable def productIsoOfEquiv [HasProduct (X ∘ e)] : ∏ᶜ (X ∘ e) ≅ ∏ᶜ X :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (isLimitFanOfEquiv X e)

noncomputable def productOptionIso {C J : Type _} [Category C]
    (X : Option J → C) [HasProduct X] [HasProduct (fun j => X (some j))]
    [HasBinaryProduct (∏ᶜ (fun j => X (some j))) (X none)] :
    (∏ᶜ X) ≅ (∏ᶜ (fun j => X (some j))) ⨯ (X none) where
  hom := prod.lift (Pi.lift (fun j => Pi.π _ (some j))) (Pi.π _ none)
  inv := Pi.lift (fun b => match b with
    | some j => prod.fst ≫ Pi.π _ j
    | none => prod.snd)

end Limits

namespace Triangulated

open Pretriangulated ObjectProperty

variable (C : Type*) [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Subcategory

variable {C}
variable (S : Subcategory C)

lemma mem_of_isZero [IsClosedUnderIsomorphisms S.P] (X : C) (hX : IsZero X) : S.P X :=
  prop_of_iso _ hX.isoZero.symm S.zero

instance : IsClosedUnderIsomorphisms S.isoClosure.P := by
  dsimp only [isoClosure]
  infer_instance

section

variable (P : C → Prop) (zero : P 0)
  (shift : ∀ (X : C) (n : ℤ), P X → P (X⟦n⟧))
  (ext₂ : ∀ (T : Triangle C) (_ : T ∈ distTriang C), P T.obj₁ → P T.obj₃ → P T.obj₂)

instance : IsClosedUnderIsomorphisms (mk' P zero shift ext₂).P where
  of_iso {X Y} e hX := by
    refine ext₂ (Triangle.mk e.hom (0 : Y ⟶ 0) 0) ?_ hX zero
    refine isomorphic_distinguished _ (contractible_distinguished X) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)

end

@[simp]
lemma shift_iff [IsClosedUnderIsomorphisms S.P] (X : C) (n : ℤ) :
    S.P (X⟦n⟧) ↔ S.P X := by
  constructor
  · intro h
    exact prop_of_iso _ ((shiftEquiv C n).unitIso.symm.app X) (S.shift _ (-n) h)
  · exact S.shift X n

/-- Variant of `mem_W_iff_of_distinguished`. -/
lemma mem_W_iff_of_distinguished'
    [IsClosedUnderIsomorphisms S.P] (T : Triangle C) (hT : T ∈ distTriang C) :
    S.W T.mor₂ ↔ S.P T.obj₁ := by
  have := S.mem_W_iff_of_distinguished _ (rot_of_distTriang _ hT)
  dsimp at this
  rw [this, shift_iff]

section

variable (T : Triangle C) (hT : T ∈ distTriang C)

include hT

omit hT in
lemma binary_product_stable [IsClosedUnderIsomorphisms S.P]
    (X₁ X₂ : C) (hX₁ : S.P X₁) (hX₂ : S.P X₂) :
    S.P (X₁ ⨯ X₂)  :=
  S.ext₂ _ (binaryProductTriangle_distinguished X₁ X₂) hX₁ hX₂

omit hT in
lemma pi_finite_stable [IsClosedUnderIsomorphisms S.P]
    {J : Type} [Finite J] (X : J → C) (hX : ∀ j, S.P (X j)) :
    S.P (∏ᶜ X) := by
  revert hX X
  let P : Type → Prop := fun J =>
    ∀ [hJ : Finite J] (X : J → C), (∀ (j : J), S.P (X j)) → S.P (∏ᶜ X)
  apply @Finite.induction_empty_option (P := P)
  · intro J₁ J₂ e hJ₁ _ X hX
    have : Finite J₁ := Finite.of_equiv _ e.symm
    exact prop_of_iso _ (productIsoOfEquiv X e) (hJ₁ (fun j₁ => X (e j₁)) (fun j₁ => hX _))
  · intro _ X _
    refine prop_of_iso _ (IsZero.isoZero ?_).symm S.zero
    rw [IsZero.iff_id_eq_zero]
    ext ⟨⟩
  · intro J _ hJ _ X hX
    exact prop_of_iso _ (productOptionIso  X).symm
      (S.binary_product_stable _ _ (hJ (fun j => X (some j)) (fun j => hX _)) (hX none))

instance : S.W.IsStableUnderFiniteProducts := by
  rw [← isoClosure_W]
  exact ⟨fun J _ => by
    refine MorphismProperty.IsStableUnderProductsOfShape.mk _ _ ?_
    intro X₁ X₂ _ _ f hf
    exact W.mk _ (productTriangle_distinguished _
      (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose))
      (pi_finite_stable _ _ (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose_spec))⟩

section

variable (S' : Subcategory C) [IsClosedUnderIsomorphisms S.P]
    [IsClosedUnderIsomorphisms S'.P]

def inter : Subcategory C :=
  mk' (fun X => S.P X ∧ S'.P X) ⟨S.zero, S'.zero⟩
    (fun X n hX => ⟨S.shift X n hX.1, S'.shift X n hX.2⟩)
    (fun T hT h₁ h₃ => ⟨S.ext₂ T hT h₁.1 h₃.1, S'.ext₂ T hT h₁.2 h₃.2⟩)

instance : IsClosedUnderIsomorphisms (S.inter S').P := by
  dsimp [inter]
  infer_instance

end

end

def category := S.P.FullSubcategory

instance : Category S.category := FullSubcategory.category _

def ι : S.category ⥤ C := ObjectProperty.ι _

def fullyFaithfulι : S.ι.FullyFaithful := ObjectProperty.fullyFaithfulι _

instance : S.ι.Full := (fullyFaithfulι _).full
instance : S.ι.Faithful := (fullyFaithfulι _).faithful

instance : Preadditive S.category := by
  dsimp [category]
  infer_instance

instance : S.ι.Additive := by
  dsimp [ι, category]
  infer_instance

lemma ι_obj_mem (X : S.category) : S.P (S.ι.obj X) := X.2

noncomputable instance hasShift : HasShift S.category ℤ :=
  S.fullyFaithfulι.hasShift (fun n => ObjectProperty.lift _ (S.ι ⋙ shiftFunctor C n)
    (fun X => S.shift _ _ X.2))
    (fun _ => ObjectProperty.liftCompιIso _ _ _)

instance commShiftι : S.ι.CommShift ℤ :=
  Functor.CommShift.of_hasShiftOfFullyFaithful _ _ _

-- these definitions are made irreducible to prevent (at least temporarily) any abuse of defeq
attribute [irreducible] hasShift commShiftι

instance (n : ℤ) : (shiftFunctor S.category n).Additive := by
  have := Functor.additive_of_iso (S.ι.commShiftIso n).symm
  apply Functor.additive_of_comp_faithful _ S.ι

instance : HasZeroObject S.category where
  zero := by
    obtain ⟨Z, hZ, mem⟩ := S.zero'
    refine ⟨⟨Z, mem⟩, ?_⟩
    rw [IsZero.iff_id_eq_zero]
    apply hZ.eq_of_src

noncomputable instance : Pretriangulated S.category where
  distinguishedTriangles := fun T => S.ι.mapTriangle.obj T ∈ distTriang C
  isomorphic_distinguished := fun T₁ hT₁ T₂ e =>
    isomorphic_distinguished _ hT₁ _ (S.ι.mapTriangle.mapIso e)
  contractible_distinguished X := by
    refine isomorphic_distinguished _ (contractible_distinguished (S.ι.obj X)) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) S.ι.mapZeroObject
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  distinguished_cocone_triangle {X Y} f := by
    obtain ⟨Z', g', h', mem⟩ := distinguished_cocone_triangle (S.ι.map f)
    obtain ⟨Z'', hZ'', ⟨e⟩⟩ := S.ext₃' _ mem X.2 Y.2
    let Z : S.category := ⟨Z'', hZ''⟩
    refine ⟨Z, S.ι.preimage (g' ≫ e.hom),
      S.ι.preimage (e.inv ≫ h' ≫ (S.ι.commShiftIso (1 : ℤ)).inv.app X),
      isomorphic_distinguished _ mem _ ?_⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  rotate_distinguished_triangle T :=
    (rotate_distinguished_triangle (S.ι.mapTriangle.obj T)).trans
      (distinguished_iff_of_iso (S.ι.mapTriangleRotateIso.app T))
  complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b comm := by
    obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := complete_distinguished_triangle_morphism (S.ι.mapTriangle.obj T₁)
      (S.ι.mapTriangle.obj T₂) hT₁ hT₂ (S.ι.map a) (S.ι.map b)
      (by simpa using S.ι.congr_map comm)
    have ⟨c', hc'⟩ : ∃ (c' : T₁.obj₃ ⟶ T₂.obj₃), c = S.ι.map c' := ⟨S.ι.preimage c, by simp⟩
    dsimp at hc₁ hc₂
    rw [hc'] at hc₁
    rw [hc', assoc, ← Functor.commShiftIso_hom_naturality] at hc₂
    refine ⟨c', ⟨S.ι.map_injective ?_, S.ι.map_injective ?_⟩⟩
    · simpa using hc₁
    · rw [← cancel_mono ((Functor.commShiftIso (ι S) (1 : ℤ)).hom.app T₂.obj₁),
        S.ι.map_comp, S.ι.map_comp, assoc, assoc, hc₂]

instance : S.ι.IsTriangulated := ⟨fun _ hT => hT⟩

instance [IsTriangulated C] : IsTriangulated S.category :=
  IsTriangulated.of_fully_faithful_triangulated_functor S.ι


section

variable {D : Type*} [Category D] [HasZeroObject D] [Preadditive D]
    [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Full]

-- note: does not require `[Faithful F]` !

def essImage : Subcategory D :=
  Subcategory.mk' F.essImage ⟨0, ⟨F.mapZeroObject⟩⟩
    (fun X n ⟨Y, ⟨e⟩⟩ => ⟨(shiftFunctor C n).obj Y,
      ⟨(F.commShiftIso n).app Y ≪≫ (shiftFunctor D n).mapIso e⟩⟩)
    (fun T hT ⟨X₁, ⟨e₁⟩⟩ ⟨X₃, ⟨e₃⟩⟩ => by
      have ⟨h, hh⟩ := F.map_surjective (e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦1⟧' ≫
        (F.commShiftIso (1 : ℤ)).inv.app X₁)
      obtain ⟨X₂, f, g, H⟩ := distinguished_cocone_triangle₂ h
      exact ⟨X₂, ⟨Triangle.π₂.mapIso
        (isoTriangleOfIso₁₃ _ _ (F.map_distinguished _ H) hT e₁ e₃ (by
          dsimp
          simp only [hh, assoc, Iso.inv_hom_id_app, Functor.comp_obj,
            comp_id, Iso.cancel_iso_hom_left, ← Functor.map_comp,
            Iso.inv_hom_id, Functor.map_id]))⟩⟩)

instance : IsClosedUnderIsomorphisms (essImage F).P  := by
  dsimp only [essImage]
  infer_instance

end

section

variable {D : Type*} [Category D] (F : D ⥤ C) (hF : ∀ (X : D), S.P (F.obj X))

def lift : D ⥤ S.category := ObjectProperty.lift S.P F hF

def liftCompInclusion : S.lift F hF ⋙ S.ι ≅ F :=   liftCompιIso _ _ _

instance [F.Faithful] : (S.lift F hF).Faithful :=
  Functor.Faithful.of_comp_iso (S.liftCompInclusion F hF)

instance [F.Full] : (S.lift F hF).Full :=
  Functor.Full.of_comp_faithful_iso (S.liftCompInclusion F hF)

-- should be generalized
instance [Preadditive D] [F.Additive] : (S.lift F hF).Additive where
  map_add {X Y f g} := by
    apply S.ι.map_injective
    apply F.map_add

noncomputable instance [HasShift D ℤ] [F.CommShift ℤ] : (S.lift F hF).CommShift ℤ :=
  Functor.CommShift.ofComp (S.liftCompInclusion F hF) ℤ

noncomputable instance [HasShift D ℤ] [F.CommShift ℤ] :
  NatTrans.CommShift (S.liftCompInclusion F hF).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _

instance isTriangulated_lift [HasShift D ℤ] [Preadditive D] [F.CommShift ℤ] [HasZeroObject D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [F.IsTriangulated]:
    (S.lift F hF).IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right (S.liftCompInclusion F hF)]
  infer_instance

end

section

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : D ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
  [IsClosedUnderIsomorphisms S.P]

def inverseImage : Subcategory D :=
  Subcategory.mk' (fun X => S.P (F.obj X))
    (prop_of_iso _ F.mapZeroObject.symm S.zero)
    (fun X n hX => prop_of_iso _ ((F.commShiftIso n).symm.app X) (S.shift _ n hX))
    (fun _ hT h₁ h₃ => S.ext₂ _ (F.map_distinguished _ hT) h₁ h₃)

lemma mem_inverseImage_iff (X : D) :
    (S.inverseImage F).P X ↔ S.P (F.obj X) := by rfl

instance : IsClosedUnderIsomorphisms (S.inverseImage F).P where
  of_iso {X Y} e hX := by
    rw [mem_inverseImage_iff] at hX ⊢
    exact prop_of_iso _ (F.mapIso e) hX

lemma mem_inverseImage_W_iff {X Y : D} (s : X ⟶ Y) :
    (S.inverseImage F).W s ↔ S.W (F.map s) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle s
  have eq₁ := (S.inverseImage F).mem_W_iff_of_distinguished _ hT
  have eq₂ := S.mem_W_iff_of_distinguished _ (F.map_distinguished _ hT)
  dsimp at eq₁ eq₂
  rw [eq₁, mem_inverseImage_iff, eq₂]

lemma inverseImage_W_isInverted {E : Type*} [Category E]
    (L : C ⥤ E) [L.IsLocalization S.W] :
    (S.inverseImage F).W.IsInvertedBy (F ⋙ L) :=
  fun X Y f hf => Localization.inverts L S.W (F.map f)
    (by simpa only [mem_inverseImage_W_iff] using hf)

end

section

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated]
  [G.IsTriangulated] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

def ofNatTrans : Subcategory C :=
  Subcategory.mk' (fun X => IsIso (τ.app X))
    ⟨0, by rw [comp_zero, ← F.map_id, id_zero, F.map_zero],
        by rw [zero_comp, ← G.map_id, id_zero, G.map_zero]⟩
    (fun X n (_ : IsIso (τ.app X)) => by
      dsimp
      rw [NatTrans.app_shift τ n]
      infer_instance)
    (fun T hT h₁ h₃ => by
      exact Pretriangulated.isIso₂_of_isIso₁₃
        ((Pretriangulated.Triangle.homMk _ _ (τ.app _) (τ.app _) (τ.app _)
          (by simp) (by simp) (by simp [NatTrans.shift_app_comm τ])))
        (F.map_distinguished _ hT) (G.map_distinguished _ hT) (by exact h₁) (by exact h₃))

instance : IsClosedUnderIsomorphisms (ofNatTrans τ).P := by
  dsimp [ofNatTrans]
  infer_instance

end

section

variable {D : Type*} [Category D] [HasZeroObject D] [Preadditive D]
    [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Full] [F.Faithful]

def map : Subcategory D := essImage (S.ι ⋙ F)

instance : IsClosedUnderIsomorphisms (S.map F).P := by
  dsimp [map]
  infer_instance

lemma mem_map_iff (X : C) [IsClosedUnderIsomorphisms S.P] :
    (S.map F).P (F.obj X) ↔ S.P X := by
  constructor
  · rintro ⟨⟨Y, hX⟩, ⟨e⟩⟩
    exact prop_of_iso _ (F.preimageIso e) hX
  · intro hX
    exact ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩

end

end Subcategory

end Triangulated

end CategoryTheory
