module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.EtaleComparison

/-!
# Interfaces for the ph/étale comparison

Typed checks expose the proper morphism property, torsion inverse-image coefficients,
and comparison situation through the shared mathematical owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open CategoryTheory.Sheaf
open AlgebraicGeometry.Scheme.PhComparison

universe u i

/- Proper morphisms in the slice category `Over S`. -/
#check (AlgebraicGeometry.Scheme.PhComparison.properOver :
    ∀ (S : Scheme.{u}),
    MorphismProperty (Over S))

/- A morphism in `Over S` is proper iff its underlying scheme morphism is proper. -/
#check (AlgebraicGeometry.Scheme.PhComparison.properOver_iff :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
    properOver S f ↔ IsProper f.left)

/- Proper morphisms in `Over S` admit pullbacks. -/
#check (AlgebraicGeometry.Scheme.PhComparison.properOver_hasPullbacks :
    ∀ (S : Scheme.{u}),
    (properOver S).HasPullbacks)

/- Proper morphisms in `Over S` are stable under base change. -/
#check (AlgebraicGeometry.Scheme.PhComparison.properOver_isStableUnderBaseChange :
    ∀ (S : Scheme.{u}),
    (properOver S).IsStableUnderBaseChange)

/- The big étale topology on `Over S` is coarser than the big ph topology. -/
#check (AlgebraicGeometry.Scheme.PhComparison.etale_le_ph :
    ∀ (S : Scheme.{u}),
    S.overGrothendieckTopology @Etale ≤ Scheme.bigPhSite S)

/- Abelian-group-valued sheafification exists on every iterated étale slice at the
topology-comparison coefficient universe. -/
#check (AlgebraicGeometry.Scheme.PhComparison.etaleSlice_hasSheafify_addCommGrp :
    ∀ {S : Scheme.{u}} (X : Over S),
    HasSheafify ((S.overGrothendieckTopology @Etale).over X)
      AddCommGrpCat.{u + 1})

/- Abelian sheaves on iterated étale slices have injective resolutions at the
topology-comparison coefficient universe. -/
#check (AlgebraicGeometry.Scheme.PhComparison.etaleSlice_hasInjectiveResolutions :
    ∀ {S : Scheme.{u}} (X : Over S),
    HasInjectiveResolutions
      (Sheaf ((S.overGrothendieckTopology @Etale).over X)
        AddCommGrpCat.{u + 1}))

/- Direct image of abelian sheaves along postcomposition on iterated étale slices
is additive. -/
#check (AlgebraicGeometry.Scheme.PhComparison.overMap_sheafPushforwardCocontinuous_additive :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      ((S.overGrothendieckTopology @Etale).over X)
      ((S.overGrothendieckTopology @Etale).over Y)).Additive)

/- The site functor `π_X` from the small étale site of `X` to the iterated étale
slice `(Sch/S)_étale / X`. -/
#check (AlgebraicGeometry.Scheme.PhComparison.piSiteFunctor :
    ∀ {S : Scheme.{u}} (X : Over S),
    X.left.Etale ⥤ Over X)

/- Forgetting the slice over `X` recovers étale relocalization into `Over S`. -/
#check (AlgebraicGeometry.Scheme.PhComparison.piSiteFunctor_forget :
    ∀ {S : Scheme.{u}} (X : Over S),
    piSiteFunctor X ⋙ Over.forget X =
      relocalizationFunctor (𝟙 X.left) ⋙ Over.map X.hom)

/- The site functor `π_X` is continuous from the small étale topology to the étale
topology on the iterated slice. -/
#check (AlgebraicGeometry.Scheme.PhComparison.piSiteFunctor_isContinuous :
    ∀ {S : Scheme.{u}} (X : Over S),
    Functor.IsContinuous (piSiteFunctor X) X.left.smallEtaleTopology
      ((S.overGrothendieckTopology @Etale).over X))

/- Étale relocalization into an iterated slice admits left Kan extensions on
abelian presheaves at the topology-comparison coefficient universe. -/
#check (AlgebraicGeometry.Scheme.PhComparison.piSiteFunctor_op_hasLeftKanExtension_addCommGrp :
    ∀ {S : Scheme.{u}} (X : Over S) (P : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
    (piSiteFunctor X).op.HasLeftKanExtension P)

/- Inverse image `π_X⁻¹` on abelian sheaves, landing in the étale iterated slice. -/
#check (AlgebraicGeometry.Scheme.PhComparison.piInverseImage :
    ∀ {S : Scheme.{u}} (X : Over S),
    Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1})

/- Inverse image `π_X⁻¹` is the sheaf pullback along `piSiteFunctor X`. -/
#check (AlgebraicGeometry.Scheme.PhComparison.piInverseImage_eq :
    ∀ {S : Scheme.{u}} (X : Over S),
    piInverseImage X =
      (piSiteFunctor X).sheafPullback AddCommGrpCat.{u + 1}
        X.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over X))

/- The coefficient family `A'_X` of sheaves on `(Sch/X)_étale` of the form `π_X⁻¹ F`
for a torsion abelian sheaf `F` on `X_étale`. -/
#check (AlgebraicGeometry.Scheme.PhComparison.torsionPiInverseImage :
    ∀ {S : Scheme.{u}} (X : Over S),
    ObjectProperty
      (Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1}))

/- Membership in `A'_X` means being isomorphic to `π_X⁻¹ F` for some torsion abelian
sheaf on the small étale site. -/
#check (AlgebraicGeometry.Scheme.PhComparison.mem_torsionPiInverseImage_iff :
    ∀ {S : Scheme.{u}} {X : Over S}
    {ℱ : Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1}},
    torsionPiInverseImage X ℱ ↔
      ∃ F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1},
        F.IsLocallyTorsion ∧ Nonempty ((piInverseImage X).obj F ≅ ℱ))

/- The inverse image of a torsion small-étale sheaf lies in `A'_X`. -/
#check (AlgebraicGeometry.Scheme.PhComparison.obj_mem_torsionPiInverseImage :
    ∀ {S : Scheme.{u}} {X : Over S}
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion),
    torsionPiInverseImage X ((piInverseImage X).obj F))

/- Each coefficient family `A'_X` is a weak Serre subcategory. -/
#check (AlgebraicGeometry.Scheme.PhComparison.torsionPiInverseImage_isWeakSerre :
    ∀ {S : Scheme.{u}} (X : Over S),
    IsWeakSerreClass (torsionPiInverseImage X))

/- Inverse image along a morphism of the slice preserves the torsion `π⁻¹`
coefficient family. -/
#check (AlgebraicGeometry.Scheme.PhComparison.torsionPiInverseImage_inverseImage_mem :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    {ℱ : Sheaf ((S.overGrothendieckTopology @Etale).over Y) AddCommGrpCat.{u + 1}}
    (hℱ : torsionPiInverseImage Y ℱ),
    torsionPiInverseImage X
      (((S.overGrothendieckTopology @Etale).overMapPullback AddCommGrpCat.{u + 1} f).obj
        ℱ))

/- A torsion `π⁻¹` coefficient sheaf on the étale slice is a sheaf for the ph
topology. -/
#check (AlgebraicGeometry.Scheme.PhComparison.torsionPiInverseImage_isSheafPh :
    ∀ {S : Scheme.{u}} {X : Over S}
    {ℱ : Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1}}
    (hℱ : torsionPiInverseImage X ℱ),
    Presheaf.IsSheaf ((Scheme.bigPhSite S).over X) ℱ.1)

/- Higher direct images along proper slice morphisms preserve the torsion `π⁻¹`
coefficient family. -/
#check (AlgebraicGeometry.Scheme.PhComparison.torsionPiInverseImage_higherDirectImage_mem :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (hf : properOver S f) (n : ℕ)
    {ℱ : Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1}}
    (hℱ : torsionPiInverseImage X ℱ),
    torsionPiInverseImage Y
      ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          ((S.overGrothendieckTopology @Etale).over X)
          ((S.overGrothendieckTopology @Etale).over Y)).rightDerived n).obj ℱ))

/- Covering refinement from a ph covering of a slice object to an étale covering
refined by proper morphisms. -/
#check (AlgebraicGeometry.Scheme.PhComparison.tau_covering_refinement :
    ∀ {S : Scheme.{u}} {U : Over S} {ι : Type i}
    (cover : ι → Over U)
    (hcover : ((Scheme.bigPhSite S).over U).CoversTop cover),
    ∃ (J : Type (max (u + 1) i)) (V : J → Over U),
      ((S.overGrothendieckTopology @Etale).over U).CoversTop V ∧
        ∃ (W : J → Over S) (f : ∀ idx, W idx ⟶ (V idx).left),
          ∀ idx,
            properOver S (f idx) ∧
              Sieve.generate (Presieve.singleton (f idx)) ∈
                  Scheme.bigPhSite S (V idx).left ∧
                ∃ (Kidx : Type (max (u + 1) i)) (Wcover : Kidx → Over (W idx)),
                  ((S.overGrothendieckTopology @Etale).over (W idx)).CoversTop
                      Wcover ∧
                    ∀ kj : Kidx,
                      ∃ i0 : ι,
                        Nonempty
                          ((Over.mk ((Wcover kj).hom ≫ f idx ≫ (V idx).hom)) ⟶
                            cover i0))

/- The ph/étale comparison on `Over S`, with proper morphisms and torsion `π⁻¹`
coefficients, satisfies the conditions of `TopologyComparison.Situation`. -/
#check (AlgebraicGeometry.Scheme.PhComparison.situation :
    ∀ (S : Scheme.{u}),
    TopologyComparison.Situation.{u + 1, u, i, max (u + 1) i, max (u + 1) i} (Scheme.bigPhSite S)
      (S.overGrothendieckTopology @Etale) (properOver S)
      (fun X ↦ torsionPiInverseImage X))

end
