import Mathlib.CategoryTheory.Shift.CommShift

open CategoryTheory Category Functor CommShift

namespace CategoryTheory

namespace Functor

section hasShiftOfFullyFaithful

variable {C D : Type _} [Category C] [Category D]
  {A : Type _} [AddMonoid A] [HasShift D A]
  {F : C ⥤ D} (hF : F.FullyFaithful)
  (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i)

namespace CommShift

def of_hasShiftOfFullyFaithful :
    letI := hF.hasShift s i; F.CommShift A := by
  letI := hF.hasShift s i
  exact
  { iso := i
    zero := by
      ext X
      simp only [comp_obj, isoZero_hom_app, ShiftMkCore.shiftFunctorZero_eq, Iso.symm_hom,
        FullyFaithful.hasShift.map_zero_hom_app, id_obj, Category.assoc,
        Iso.hom_inv_id_app, Category.comp_id]
    add := fun a b => by
      ext X
      simp only [comp_obj, isoAdd_hom_app, ShiftMkCore.shiftFunctorAdd_eq, Iso.symm_hom,
        FullyFaithful.hasShift.map_add_hom_app, Category.assoc, ShiftMkCore.shiftFunctor_eq,
        Iso.inv_hom_id_app_assoc, ← (shiftFunctor D b).map_comp_assoc, Iso.inv_hom_id_app,
        Functor.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id] }

end CommShift

lemma shiftFunctorIso_of_hasShiftOfFullyFaithful (a : A) :
    letI := hF.hasShift s i;
    letI := CommShift.of_hasShiftOfFullyFaithful hF s i;
    F.commShiftIso a = i a := by
  rfl

end hasShiftOfFullyFaithful

end Functor

namespace Functor

namespace CommShift

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
  [Full G] [Faithful G]
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A]
  [G.CommShift A] [H.CommShift A]

namespace OfComp

variable {A}

noncomputable def iso (a : A) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  ((whiskeringRight C D E).obj G).preimageIso (Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ e ≪≫
    H.commShiftIso a ≪≫ isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft F (G.commShiftIso a).symm ≪≫ (Functor.associator _ _ _).symm)

@[simp]
lemma map_iso_hom_app (a : A) (X : C) :
    G.map ((iso e a).hom.app X) = e.hom.app (X⟦a⟧) ≫
      (H.commShiftIso a).hom.app X ≫ (e.inv.app X)⟦a⟧' ≫
      (G.commShiftIso a).inv.app (F.obj X) := by
  have h : ((whiskeringRight C D E).obj G).map (iso e a).hom = _ :=
    Functor.map_preimage _ _
  simpa using congr_app h X

@[simp]
lemma map_iso_inv_app (a : A) (X : C) :
    G.map ((iso e a).inv.app X) =
      (G.commShiftIso a).hom.app (F.obj X) ≫ (e.hom.app X)⟦a⟧' ≫
      (H.commShiftIso a).inv.app X ≫ e.inv.app (X⟦a⟧) := by
  have h : ((whiskeringRight C D E).obj G).map (iso e a).inv = _ :=
    Functor.map_preimage _ _
  simpa using congr_app h X

attribute [irreducible] iso

end OfComp

noncomputable def ofComp : F.CommShift A where
  iso := OfComp.iso e
  zero := by
    ext X
    apply G.map_injective
    simp [G.commShiftIso_zero, H.commShiftIso_zero]
  add a b := by
    ext X
    apply G.map_injective
    simp only [comp_obj, OfComp.map_iso_hom_app, H.commShiftIso_add, isoAdd_hom_app,
      G.commShiftIso_add, isoAdd_inv_app, NatTrans.naturality_assoc, comp_map, assoc,
      Iso.inv_hom_id_app_assoc, map_comp]
    erw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
    dsimp
    simp only [← Functor.map_comp_assoc]
    congr 4
    simp

lemma ofComp_compatibility :
    letI := ofComp e
    NatTrans.CommShift e.hom A := by
  letI := ofComp e
  refine ⟨fun a => ?_⟩
  ext X
  have : commShiftIso F a = OfComp.iso e a := rfl
  simp only [comp_obj, NatTrans.comp_app, commShiftIso_comp_hom_app, this,
    OfComp.map_iso_hom_app, assoc, Iso.inv_hom_id_app, comp_id, whiskerRight_app,
    whiskerLeft_app, NatIso.cancel_natIso_hom_left, ← Functor.map_comp,
    Functor.map_id]

end CommShift

end Functor

end CategoryTheory
