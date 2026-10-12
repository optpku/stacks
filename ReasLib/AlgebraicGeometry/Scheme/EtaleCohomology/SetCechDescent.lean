/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.EtaleCohomology.CechDescent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsPullback
public import ReasLib.CategoryTheory.Limits.Shapes.Equalizer

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [finiteMorphism : IsFinite f] [surjectiveMorphism : Surjective f]
variable [(Arrow.mk f).HasCechNerve]
variable [HasWeakSheafify Y.smallEtaleTopology (Type u)]
variable [∀ n : ℕ, HasWeakSheafify (finiteCechScheme f n).smallEtaleTopology (Type u)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type u, ∀ n : ℕ,
  (smallEtalePullback (finiteCechMap f n)).op.HasLeftKanExtension P]
variable [∀ n m : ℕ, ∀ P : (finiteCechScheme f n).Etaleᵒᵖ ⥤ Type u,
  ∀ α : ⦋n⦌ ⟶ ⦋m⦌,
    (smallEtalePullback (finiteCechNerve_map f α)).op.HasLeftKanExtension P]
variable (G : Sheaf Y.smallEtaleTopology (Type u))

/-- Inverse image `f_n^{-1} G` of an étale sheaf of sets along a Čech-nerve projection. -/
abbrev finiteCechSetInverseImage (n : ℕ) :
    Sheaf (finiteCechScheme f n).smallEtaleTopology (Type u) :=
  (Sheaf.smallEtaleInverseImage (finiteCechMap f n) (Type u)).obj G

/-- The sheaf `f_{n,*} f_n^{-1} G` on `Y_étale`. -/
abbrev finiteCechSetSheaf (n : ℕ) :
    Sheaf Y.smallEtaleTopology (Type u) :=
  ((smallEtalePullback (finiteCechMap f n)).sheafPushforwardContinuous (Type u)
      Y.smallEtaleTopology (finiteCechScheme f n).smallEtaleTopology).obj
    (finiteCechSetInverseImage f G n)

/-- The adjunction unit `G ⟶ f_{n,*} f_n^{-1} G`. -/
abbrev finiteCechSet_unit (n : ℕ) :
    G ⟶ finiteCechSetSheaf f G n :=
  ((smallEtalePullback (finiteCechMap f n)).sheafAdjunctionContinuous (Type u)
      Y.smallEtaleTopology (finiteCechScheme f n).smallEtaleTopology).unit.app G

/-- Site-functor isomorphism for a Čech-nerve operator over `Y`. -/
abbrev finiteCechSet_pullbackCompIso {n m : SimplexCategory} (α : n ⟶ m) :
    smallEtalePullback (finiteCechMap f m.len) ≅
      smallEtalePullback (finiteCechMap f n.len) ⋙
        smallEtalePullback (finiteCechNerve_map f α) :=
  MorphismProperty.Over.pullbackComp
    (finiteCechNerve_map f α) (finiteCechMap f n.len)
    (finiteCechMap f m.len) (finiteCechNerve_map_comp_base f α).symm

/-- Sequential inverse image along a Čech-nerve operator. -/
abbrev finiteCechSetInverseImage_comp {n m : SimplexCategory} (α : n ⟶ m) :
    Sheaf (finiteCechScheme f m.len).smallEtaleTopology (Type u) :=
  (Sheaf.smallEtaleInverseImage (finiteCechNerve_map f α) (Type u)).obj
    (finiteCechSetInverseImage f G n.len)

/-- Identification `g^{-1} f_n^{-1} G ≅ f_m^{-1} G` for a Čech-nerve operator `g`. -/
noncomputable def finiteCechSetInverseImage_iso {n m : SimplexCategory} (α : n ⟶ m) :
    finiteCechSetInverseImage_comp f G α ≅ finiteCechSetInverseImage f G m.len :=
  let basePullback := smallEtalePullback (finiteCechMap f n.len)
  let operatorPullback := smallEtalePullback (finiteCechNerve_map f α)
  let compositeContinuous := Functor.isContinuous_comp basePullback operatorPullback
    Y.smallEtaleTopology (finiteCechScheme f n.len).smallEtaleTopology
    (finiteCechScheme f m.len).smallEtaleTopology
  let baseAdjunction := basePullback.sheafAdjunctionContinuous (Type u)
    Y.smallEtaleTopology (finiteCechScheme f n.len).smallEtaleTopology
  let operatorAdjunction := operatorPullback.sheafAdjunctionContinuous (Type u)
    (finiteCechScheme f n.len).smallEtaleTopology
    (finiteCechScheme f m.len).smallEtaleTopology
  let sequentialAdjunction := (baseAdjunction.comp operatorAdjunction).ofNatIsoRight
    (Functor.sheafPushforwardContinuousComp basePullback operatorPullback (Type u)
      Y.smallEtaleTopology (finiteCechScheme f n.len).smallEtaleTopology
      (finiteCechScheme f m.len).smallEtaleTopology)
  let directAdjunction := (smallEtalePullback (finiteCechMap f m.len)).sheafAdjunctionContinuous
    (Type u) Y.smallEtaleTopology (finiteCechScheme f m.len).smallEtaleTopology
  let transportedAdjunction := directAdjunction.ofNatIsoRight
    (@Functor.sheafPushforwardContinuousIso _ _ _ _ _ _
      (finiteCechSet_pullbackCompIso f α) (Type u) inferInstance
      Y.smallEtaleTopology (finiteCechScheme f m.len).smallEtaleTopology
      inferInstance compositeContinuous)
  (Adjunction.leftAdjointUniq sequentialAdjunction transportedAdjunction).app G

/-- Face-induced map `f_{n,*} f_n^{-1} G ⟶ f_{m,*} f_m^{-1} G` of set-valued Čech sheaves. -/
noncomputable def finiteCechSetSheaf_map {n m : SimplexCategory} (α : n ⟶ m) :
    finiteCechSetSheaf f G n.len ⟶ finiteCechSetSheaf f G m.len :=
  let operatorPullback := smallEtalePullback (finiteCechNerve_map f α)
  let basePullback := smallEtalePullback (finiteCechMap f n.len)
  let compositeContinuous := Functor.isContinuous_comp basePullback operatorPullback
    Y.smallEtaleTopology (finiteCechScheme f n.len).smallEtaleTopology
    (finiteCechScheme f m.len).smallEtaleTopology
  (basePullback.sheafPushforwardContinuous (Type u)
      Y.smallEtaleTopology (finiteCechScheme f n.len).smallEtaleTopology).map
    ((operatorPullback.sheafAdjunctionContinuous (Type u)
        (finiteCechScheme f n.len).smallEtaleTopology
        (finiteCechScheme f m.len).smallEtaleTopology).unit.app
      (finiteCechSetInverseImage f G n.len)) ≫
    (Functor.sheafPushforwardContinuousComp basePullback operatorPullback (Type u)
        Y.smallEtaleTopology (finiteCechScheme f n.len).smallEtaleTopology
        (finiteCechScheme f m.len).smallEtaleTopology).hom.app
      (finiteCechSetInverseImage_comp f G α) ≫
    (@Functor.sheafPushforwardContinuousIso _ _ _ _ _ _
        (finiteCechSet_pullbackCompIso f α).symm (Type u) inferInstance
        Y.smallEtaleTopology (finiteCechScheme f m.len).smallEtaleTopology
        compositeContinuous inferInstance).hom.app
      (finiteCechSetInverseImage_comp f G α) ≫
    ((smallEtalePullback (finiteCechMap f m.len)).sheafPushforwardContinuous (Type u)
        Y.smallEtaleTopology (finiteCechScheme f m.len).smallEtaleTopology).map
      (finiteCechSetInverseImage_iso f G α).hom

/-- The two coface maps `f_{0,*} f_0^{-1} G ⇉ f_{1,*} f_1^{-1} G`. -/
abbrev finiteCechSetSheaf_face (i : Fin 2) :
    finiteCechSetSheaf f G 0 ⟶ finiteCechSetSheaf f G 1 :=
  finiteCechSetSheaf_map f G (SimplexCategory.δ i)

/-- The unit `G ⟶ f_{0,*} f_0^{-1} G` equalizes the two coface maps. -/
theorem finiteCechSetSheaf_face_equalizes :
    finiteCechSet_unit f G 0 ≫ finiteCechSetSheaf_face f G 0 =
      finiteCechSet_unit f G 0 ≫ finiteCechSetSheaf_face f G 1 :=
  sorry

/-- Identification of `Γ(Y, f_{n,*} f_n^{-1} G)` with sections of `f_n^{-1} G`
at the pullback of the identity étale object of `Y`. -/
abbrev finiteCechSet_pushforwardSectionsIso (n : ℕ) :
    etaleGlobalSections (finiteCechSetSheaf f G n) ≅
      etalePullbackIdentitySections (finiteCechMap f n) G :=
  (smallEtalePullback (finiteCechMap f n)).sheafPushforwardContinuousObjObjIso (Type u)
    (finiteCechSetInverseImage f G n)
    (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)

/-- Parallel pair on inverse-image sections induced by the two cofaces. -/
noncomputable def finiteCechSet_invImage_face (i : Fin 2) :
    etalePullbackIdentitySections (finiteCechMap f 0) G ⟶
      etalePullbackIdentitySections (finiteCechMap f 1) G :=
  (finiteCechSet_pushforwardSectionsIso f G 0).inv ≫
    TypeCat.ofHom
      ((finiteCechSetSheaf_face f G i).hom.app
        (op (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance))) ≫
    (finiteCechSet_pushforwardSectionsIso f G 1).hom

/-- Pullback of global sections along `f_0` equalizes the two coface maps on
inverse-image sections. -/
theorem finiteCechSet_invImage_face_equalizes :
    TypeCat.ofHom (etaleSectionsPullback (finiteCechMap f 0) G) ≫
        finiteCechSet_invImage_face f G 0 =
      TypeCat.ofHom (etaleSectionsPullback (finiteCechMap f 0) G) ≫
        finiteCechSet_invImage_face f G 1 :=
  sorry

include finiteMorphism surjectiveMorphism

/-- A sheaf of sets on `Y_étale` is the equalizer of the two direct-image coface maps
for the Čech nerve of a finite surjective morphism. -/
theorem finiteCech_setSheaf_isEqualizer :
    IsEqualizer (finiteCechSet_unit f G 0)
      (finiteCechSetSheaf_face f G 0) (finiteCechSetSheaf_face f G 1)
      (finiteCechSetSheaf_face_equalizes f G) :=
  sorry

/-- Global sections of an étale sheaf of sets form the equalizer of the two coface
maps on inverse-image sections for the Čech nerve of a finite surjective morphism. -/
theorem finiteCech_setSheaf_globalSections_equalizer :
    IsEqualizer (TypeCat.ofHom (etaleSectionsPullback (finiteCechMap f 0) G))
      (finiteCechSet_invImage_face f G 0) (finiteCechSet_invImage_face f G 1)
      (finiteCechSet_invImage_face_equalizes f G) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
