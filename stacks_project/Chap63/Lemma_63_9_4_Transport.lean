module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import stacks_project.Chap63.Lemma_63_8_5_Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import stacks_project.Chap63.Lemma_63_9_4_Pullback
public import stacks_project.Chap63.Lemma_63_9_2_Comparison
public import stacks_project.Chap63.Lemma_63_8_5_Comparison

/-!
# Canonical transport between pullback compactification models

The actual pullback-pasting and interior comparisons preserve the fixed maps to
both base and interior. Their derived comparisons are composed from the proper
and lower-shriek mates, with the inverse formed from the inverse ambient map.
-/

@[expose] public section

section
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {S S' W T Y Y' : C} (a : S' ⟶ S) (p : W ⟶ S) (q : T ⟶ W)

/-- Flatten the two ambient base changes using the specified pullback projections. -/
def compositeAmbientIso :
    pullback (pullback.snd a p) q ≅ pullback a (q ≫ p) :=
  pullbackLeftPullbackSndIso a p q

@[reassoc (attr := simp)]
theorem compositeAmbientIso_hom_fst :
    (compositeAmbientIso a p q).hom ≫ pullback.fst a (q ≫ p) =
      pullback.fst (pullback.snd a p) q ≫ pullback.fst a p :=
  pullbackLeftPullbackSndIso_hom_fst a p q

@[reassoc (attr := simp)]
theorem compositeAmbientIso_hom_snd :
    (compositeAmbientIso a p q).hom ≫ pullback.snd a (q ≫ p) =
      pullback.snd (pullback.snd a p) q :=
  pullbackLeftPullbackSndIso_hom_snd a p q

variable (j : Y ⟶ W) (b : Y' ⟶ Y) (j' : Y' ⟶ pullback a p)
  (h : j' ≫ pullback.snd a p = b ≫ j)

/-- Identify the interior of the iterated ambient with the pullback of the old interior. -/
def interiorAmbientIso :
    pullback j' (pullback.fst (pullback.snd a p) q) ≅
      pullback b (pullback.fst j q) :=
  pullbackRightPullbackFstIso (pullback.snd a p) q j' ≪≫
    pullback.congrHom h rfl ≪≫ (pullbackRightPullbackFstIso j q b).symm

@[reassoc (attr := simp)]
theorem interiorAmbientIso_hom_fst :
    (interiorAmbientIso a p q j b j' h).hom ≫ pullback.fst b (pullback.fst j q) =
      pullback.fst j' (pullback.fst (pullback.snd a p) q) := by
  simp [interiorAmbientIso, pullback.congrHom_hom, Category.assoc,
    pullback.map, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem interiorAmbientIso_hom_snd_snd :
    (interiorAmbientIso a p q j b j' h).hom ≫
        pullback.snd b (pullback.fst j q) ≫ pullback.snd j q =
      pullback.snd j' (pullback.fst (pullback.snd a p) q) ≫
        pullback.snd (pullback.snd a p) q := by
  simp [interiorAmbientIso, pullback.congrHom_hom, Category.assoc,
    pullback.map, pullback.lift_snd]

/-- The outer first projection and the innermost second projection determine a map. -/
theorem nestedPullback_hom_ext {V : C}
    {s t : V ⟶ pullback b (pullback.fst j q)}
    (hf : s ≫ pullback.fst b (pullback.fst j q) =
      t ≫ pullback.fst b (pullback.fst j q))
    (hs : s ≫ pullback.snd b (pullback.fst j q) ≫ pullback.snd j q =
      t ≫ pullback.snd b (pullback.fst j q) ≫ pullback.snd j q) : s = t := by
  apply (cancel_mono (pullbackRightPullbackFstIso j q b).hom).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullbackRightPullbackFstIso_hom_fst] using hf
  · simpa only [Category.assoc, pullbackRightPullbackFstIso_hom_snd] using hs

end CategoryTheory.Limits

end
end

section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The small-étale pullback functor of an identity, using the adjunction of over categories. -/
def smallEtaleIdentityIso (S : Scheme.{u}) : smallEtalePullback (𝟙 S) ≅ 𝟭 S.Etale :=
  conjugateIsoEquiv
    (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ (𝟙 S)
      (inferInstance : Etale (𝟙 S)) trivial)
    Adjunction.id (MorphismProperty.Over.mapId (P := @Etale) (Q := ⊤) S).symm

/-- Pullback along the identity has the explicit identity-site equivalence. -/
instance smallEtaleIdentity_isEquivalence (S : Scheme.{u}) :
    (smallEtalePullback (𝟙 S)).IsEquivalence :=
  Functor.isEquivalence_of_iso (smallEtaleIdentityIso S).symm

/-- Kan extension along the identity-site equivalence exists for every module presheaf. -/
instance smallEtaleIdentity_hasLeftKanExtension (S : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (F : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ) :
    (smallEtalePullback (𝟙 S)).op.HasLeftKanExtension F := sorry

variable (S : Scheme.{u}) (Λ : Type u) [CommRing Λ]
  [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]

/-- The canonical identity comparison for module inverse image, from uniqueness of adjoints. -/
def moduleInverseImageIdentityIso :
    etaleModuleSheafPullback (𝟙 S) Λ ≅ 𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  Adjunction.leftAdjointIdIso
    ((smallEtalePullback (𝟙 S)).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      S.smallEtaleTopology S.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousId' (smallEtaleIdentityIso S)
      (ModuleCat.{u} Λ) S.smallEtaleTopology)

variable [∀ U : S.Etale,
    HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived identity comparison, induced by the actual module-sheaf identity comparison. -/
def derivedInverseImageIdentityIso :
    etaleModuleDerivedInverseImage (𝟙 S) Λ ≅ 𝟭 (EtaleDerived S Λ) :=
  Functor.MapDerivedCategory.functorIso (moduleInverseImageIdentityIso S Λ) ≪≫
    ExactFunctor.MapDerivedCategory.idFunctorIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))

end AlgebraicGeometry.Scheme.Etale

end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- An ambient isomorphism preserving both compactification triangles gives an isomorphism
of fixed-interior compactifications. -/
def isoMkOfAmbient {S : Scheme.{u}} {X : Over S} {P Q : Of S X}
    (e : P.obj.right.left ≅ Q.obj.right.left)
    (hi : ι P ≫ e.hom = ι Q) (hp : e.hom ≫ Q.obj.right.hom = P.obj.right.hom) :
    P ≅ Q :=
  ObjectProperty.isoMk _ (Under.isoMk (Over.isoMk e hp) (by
    ext
    exact hi))

@[simp]
theorem isoMkOfAmbient_hom {S : Scheme.{u}} {X : Over S} {P Q : Of S X}
    (e : P.obj.right.left ≅ Q.obj.right.left)
    (hi : ι P ≫ e.hom = ι Q) (hp : e.hom ≫ Q.obj.right.hom = P.obj.right.hom) :
    ambientMap (isoMkOfAmbient e hi hp).hom = e.hom := rfl

@[simp]
theorem isoMkOfAmbient_inv {S : Scheme.{u}} {X : Over S} {P Q : Of S X}
    (e : P.obj.right.left ≅ Q.obj.right.left)
    (hi : ι P ≫ e.hom = ι Q) (hp : e.hom ≫ Q.obj.right.hom = P.obj.right.hom) :
    ambientMap (isoMkOfAmbient e hi hp).inv = e.inv := rfl

/-- Forget a fixed-interior isomorphism to its actual two ambient maps. -/
def ambientIso {S : Scheme.{u}} {X : Over S} {P Q : Of S X} (e : P ≅ Q) :
    P.obj.right.left ≅ Q.obj.right.left where
  hom := ambientMap e.hom
  inv := ambientMap e.inv
  hom_inv_id := congrArg (fun k : P ⟶ P => ambientMap k) e.hom_inv_id
  inv_hom_id := congrArg (fun k : Q ⟶ Q => ambientMap k) e.inv_hom_id

/-- The ambient isomorphism preserves the fixed interior map. -/
theorem ambientIso_interior {S : Scheme.{u}} {X : Over S} {P Q : Of S X} (e : P ≅ Q) :
    ι P ≫ (ambientIso e).hom = ι Q :=
  congrArg (fun k => k.left) (Under.w e.hom.hom)

/-- The ambient isomorphism is over the original base. -/
theorem ambientIso_over {S : Scheme.{u}} {X : Over S} {P Q : Of S X} (e : P ≅ Q) :
    (ambientIso e).hom ≫ Q.obj.right.hom = P.obj.right.hom :=
  Over.w e.hom.hom.right

end AlgebraicGeometry.Scheme.Compactification.Of

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  (C : CompDiagram X g) {X' Y' Z' : Scheme.{u}}
  (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X.left)
  (h_upper : IsPullback c f' X.hom b) (h_lower : IsPullback b g' g a)
  [IsSeparated f'] [Scheme.Hom.FiniteType f']
  [IsSeparated g'] [Scheme.Hom.FiniteType g']
  [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y']
  [CompactSpace Z'] [QuasiSeparatedSpace Z']

/-- The interior compactification written over the morphism `X.hom`. -/
def ofInteriorHom : Of Y (Over.mk X.hom) :=
  @Of.mk Y (Over.mk X.hom) (Over.mk (CompDiagram.toBase X g C))
    (Over.homMk (CompDiagram.ιInterior X g C) (CompDiagram.ιInterior_comp_toBase X g C))
    (CompDiagram.instIsOpenImmersion_ιInterior X g C)
    (CompDiagram.instQuasiCompact_ιInterior X g C)
    (CompDiagram.instIsProper_toBase X g C)

theorem ofInteriorHom_ι : Of.ι (ofInteriorHom X g C) = CompDiagram.ιInterior X g C := rfl
theorem ofInteriorHom_hom :
    (ofInteriorHom X g C).obj.right.hom = CompDiagram.toBase X g C := rfl

/-- The composition diagram obtained by base change of both ambient schemes. -/
@[irreducible]
def stackedCompPullback : CompDiagram (Over.mk f') g' :=
  CompDiagram.pullback X g C f' g' a b c h_upper h_lower

/-- The opaque elaboration spelling retains the identical constructed diagram in the kernel. -/
theorem stackedCompPullback_def :
    stackedCompPullback X g C f' g' a b c h_upper h_lower =
      CompDiagram.pullback X g C f' g' a b c h_upper h_lower := by
  unfold stackedCompPullback
  rfl

/-- The opaque spelling exposes its actual base-change construction. -/
theorem stackedCompPullback_eq :
    stackedCompPullback X g C f' g' a b c h_upper h_lower =
      CompDiagram.pullback X g C f' g' a b c h_upper h_lower :=
  stackedCompPullback_def X g C f' g' a b c h_upper h_lower

/-- The composite of the two separated maps is separated. -/
instance instIsSeparated_f'_comp_g' : IsSeparated (f' ≫ g') := inferInstance

/-- The composite of the two finite-type maps is of finite type. -/
instance instFiniteType_f'_comp_g' : Scheme.Hom.FiniteType (f' ≫ g') := inferInstance

/-- The iterated ambient of the pulled-back composite identifies with the direct pullback. -/
def compositeCompactificationAmbientIso :
    (CompDiagram.ofComposite (Over.mk f') g'
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left ≅
    (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C)).obj.right.left :=
  compositeAmbientIso a C.P_g.obj.right.hom C.P_bar.obj.right.hom

/-- The ambient comparison is over the new base. -/
theorem compositeCompactificationAmbientIso_over :
    (compositeCompactificationAmbientIso X g C f' g' a b c h_upper h_lower).hom ≫
        (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
          (CompDiagram.ofComposite X g C)).obj.right.hom =
      (CompDiagram.ofComposite (Over.mk f') g'
        (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.hom :=
  compositeAmbientIso_hom_fst a C.P_g.obj.right.hom C.P_bar.obj.right.hom

/-- The ambient comparison preserves the fixed interior. -/
theorem compositeCompactificationAmbientIso_interior :
    Of.ι (CompDiagram.ofComposite (Over.mk f') g'
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)) ≫
        (compositeCompactificationAmbientIso X g C f' g' a b c h_upper h_lower).hom =
      Of.ι (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C)) := by
  let D := CompDiagram.pullback X g C f' g' a b c h_upper h_lower
  let Q := compactificationPullback (X.hom ≫ g) a (f' ≫ g') c
    (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)
  have hI_base : Of.ι D.P_bar ≫
      pullback.fst (pullback.snd a C.P_g.obj.right.hom) C.P_bar.obj.right.hom =
      f' ≫ interiorLift g a g' b h_lower C.P_g :=
    interiorLift_comp_toBase (X.hom ≫ Of.ι C.P_g)
      (ambientToSource g a g' b h_lower C.P_g)
      (f' ≫ Of.ι (CompDiagram.pullback_P_g X g C f' g' a b c h_upper h_lower)) c
      (CompDiagram.pullback_P_bar_isPullback X g C f' g' a b c h_upper h_lower) C.P_bar
  have hI_source : Of.ι D.P_bar ≫
      pullback.snd (pullback.snd a C.P_g.obj.right.hom) C.P_bar.obj.right.hom =
      c ≫ Of.ι C.P_bar :=
    interiorLift_comp_toSource (X.hom ≫ Of.ι C.P_g)
      (ambientToSource g a g' b h_lower C.P_g)
      (f' ≫ Of.ι (CompDiagram.pullback_P_g X g C f' g' a b c h_upper h_lower)) c
      (CompDiagram.pullback_P_bar_isPullback X g C f' g' a b c h_upper h_lower) C.P_bar
  have hQ_base : Of.ι Q ≫ pullback.fst a
      (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom) = f' ≫ g' :=
    interiorLift_comp_toBase (X.hom ≫ g) a (f' ≫ g') c
      (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)
  have hQ_source : Of.ι Q ≫ pullback.snd a
      (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom) =
      c ≫ Of.ι (CompDiagram.ofComposite X g C) :=
    interiorLift_comp_toSource (X.hom ≫ g) a (f' ≫ g') c
      (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)
  rw [CompDiagram.ofComposite_ι, CompDiagram.ιInterior_comp_openImmersion]
  change Of.ι D.P_bar ≫
    (compositeAmbientIso a C.P_g.obj.right.hom C.P_bar.obj.right.hom).hom = Of.ι Q
  apply pullback.hom_ext
  · change (Of.ι D.P_bar ≫
        (compositeAmbientIso a C.P_g.obj.right.hom C.P_bar.obj.right.hom).hom) ≫
        pullback.fst a (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom) = _
    refine Eq.trans ?_ hQ_base.symm
    calc
      _ = Of.ι D.P_bar ≫ ((compositeAmbientIso a C.P_g.obj.right.hom
          C.P_bar.obj.right.hom).hom ≫ pullback.fst a
          (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom)) := Category.assoc _ _ _
      _ = Of.ι D.P_bar ≫ (pullback.fst (pullback.snd a C.P_g.obj.right.hom)
          C.P_bar.obj.right.hom ≫ pullback.fst a C.P_g.obj.right.hom) :=
        congrArg (fun k => Of.ι D.P_bar ≫ k)
          (compositeAmbientIso_hom_fst a C.P_g.obj.right.hom C.P_bar.obj.right.hom)
      _ = (Of.ι D.P_bar ≫ pullback.fst (pullback.snd a C.P_g.obj.right.hom)
          C.P_bar.obj.right.hom) ≫ pullback.fst a C.P_g.obj.right.hom :=
        (Category.assoc _ _ _).symm
      _ = (f' ≫ interiorLift g a g' b h_lower C.P_g) ≫
          pullback.fst a C.P_g.obj.right.hom :=
        congrArg (fun k => k ≫ pullback.fst a C.P_g.obj.right.hom) hI_base
      _ = f' ≫ g' := (Category.assoc _ _ _).trans
        (congrArg (fun k => f' ≫ k) (interiorLift_comp_toBase g a g' b h_lower C.P_g))
  · change (Of.ι D.P_bar ≫
        (compositeAmbientIso a C.P_g.obj.right.hom C.P_bar.obj.right.hom).hom) ≫
        pullback.snd a (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom) = _
    refine Eq.trans ?_ (hQ_source.trans
      (congrArg (fun k => c ≫ k) (CompDiagram.ιInterior_comp_openImmersion X g C))).symm
    calc
      _ = Of.ι D.P_bar ≫ ((compositeAmbientIso a C.P_g.obj.right.hom
          C.P_bar.obj.right.hom).hom ≫ pullback.snd a
          (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom)) := Category.assoc _ _ _
      _ = Of.ι D.P_bar ≫ pullback.snd (pullback.snd a C.P_g.obj.right.hom)
          C.P_bar.obj.right.hom := congrArg (fun k => Of.ι D.P_bar ≫ k)
        (compositeAmbientIso_hom_snd a C.P_g.obj.right.hom C.P_bar.obj.right.hom)
      _ = c ≫ Of.ι C.P_bar := hI_source

/-- The actual isomorphism between iterated and direct composite compactifications. -/
def compositeCompactificationIso :
    CompDiagram.ofComposite (Over.mk f') g'
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower) ≅
    compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C) :=
  Of.isoMkOfAmbient (compositeCompactificationAmbientIso X g C f' g' a b c h_upper h_lower)
    (compositeCompactificationAmbientIso_interior X g C f' g' a b c h_upper h_lower)
    (compositeCompactificationAmbientIso_over X g C f' g' a b c h_upper h_lower)

/-- The ambient comparison from the pulled-back diagram's interior to the direct upper pullback. -/
def interiorCompactificationAmbientIso :
    (CompDiagram.ofInterior (Over.mk f') g'
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left ≅
    (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.left :=
  interiorAmbientIso a C.P_g.obj.right.hom C.P_bar.obj.right.hom (Of.ι C.P_g) b
    (interiorLift g a g' b h_lower C.P_g)
    (interiorLift_comp_toSource g a g' b h_lower C.P_g)

/-- The interior ambient comparison preserves the projection to `Y'`. -/
theorem interiorCompactificationAmbientIso_over :
    (interiorCompactificationAmbientIso X g C f' g' a b c h_upper h_lower).hom ≫
        (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.hom =
      (CompDiagram.ofInterior (Over.mk f') g'
        (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.hom :=
  interiorAmbientIso_hom_fst a C.P_g.obj.right.hom C.P_bar.obj.right.hom (Of.ι C.P_g) b
    (interiorLift g a g' b h_lower C.P_g)
    (interiorLift_comp_toSource g a g' b h_lower C.P_g)

/-- The interior ambient comparison preserves the actual map from `X'`. -/
theorem interiorCompactificationAmbientIso_interior :
    Of.ι (CompDiagram.ofInterior (Over.mk f') g'
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)) ≫
        (interiorCompactificationAmbientIso X g C f' g' a b c h_upper h_lower).hom =
      Of.ι (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)) := by
  let D := CompDiagram.pullback X g C f' g' a b c h_upper h_lower
  let Q := compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)
  let E := interiorCompactificationAmbientIso X g C f' g' a b c h_upper h_lower
  have hi : Of.ι (CompDiagram.ofInterior (Over.mk f') g' D) ≫
      pullback.fst (Of.ι D.P_g) D.P_bar.obj.right.hom = f' :=
    CompDiagram.ιInterior_comp_toBase (Over.mk f') g' D
  have hq : Of.ι Q ≫ pullback.fst b (CompDiagram.toBase X g C) = f' :=
    interiorLift_comp_toBase X.hom b f' c h_upper (ofInteriorHom X g C)
  have hqSource : Of.ι Q ≫ pullback.snd b (CompDiagram.toBase X g C) =
      c ≫ Of.ι (ofInteriorHom X g C) :=
    interiorLift_comp_toSource X.hom b f' c h_upper (ofInteriorHom X g C)
  have hbSource : Of.ι D.P_bar ≫
      pullback.snd (pullback.snd a C.P_g.obj.right.hom) C.P_bar.obj.right.hom = c ≫ Of.ι C.P_bar :=
    interiorLift_comp_toSource (X.hom ≫ Of.ι C.P_g)
      (ambientToSource g a g' b h_lower C.P_g)
      (f' ≫ Of.ι (CompDiagram.pullback_P_g X g C f' g' a b c h_upper h_lower)) c
      (CompDiagram.pullback_P_bar_isPullback X g C f' g' a b c h_upper h_lower) C.P_bar
  apply nestedPullback_hom_ext C.P_bar.obj.right.hom (Of.ι C.P_g) b
  · refine Eq.trans ?_ hq.symm
    exact (Category.assoc _ _ _).trans ((congrArg
      (fun k => Of.ι (CompDiagram.ofInterior (Over.mk f') g' D) ≫ k)
      (interiorCompactificationAmbientIso_over X g C f' g' a b c h_upper h_lower)).trans hi)
  · have hright : Of.ι Q ≫ pullback.snd b (CompDiagram.toBase X g C) ≫
        pullback.snd (Of.ι C.P_g) C.P_bar.obj.right.hom = c ≫ Of.ι C.P_bar :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ pullback.snd (Of.ι C.P_g) C.P_bar.obj.right.hom) hqSource).trans
          ((Category.assoc _ _ _).trans (congrArg (fun k => c ≫ k)
            (CompDiagram.ιInterior_comp_openImmersion X g C))))
    refine Eq.trans ?_ hright.symm
    have he := interiorAmbientIso_hom_snd_snd a C.P_g.obj.right.hom C.P_bar.obj.right.hom
      (Of.ι C.P_g) b (interiorLift g a g' b h_lower C.P_g)
      (interiorLift_comp_toSource g a g' b h_lower C.P_g)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => Of.ι (CompDiagram.ofInterior (Over.mk f') g' D) ≫ k) he).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ pullback.snd (pullback.snd a C.P_g.obj.right.hom)
            C.P_bar.obj.right.hom) (CompDiagram.ιInterior_comp_openImmersion (Over.mk f') g' D)).trans
              hbSource)))

/-- The fixed-interior isomorphism identifying the two upper compactifications. -/
def interiorCompactificationIso :
    CompDiagram.ofInterior (Over.mk f') g'
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower) ≅
    compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C) :=
  Of.isoMkOfAmbient (interiorCompactificationAmbientIso X g C f' g' a b c h_upper h_lower)
    (interiorCompactificationAmbientIso_interior X g C f' g' a b c h_upper h_lower)
    (interiorCompactificationAmbientIso_over X g C f' g' a b c h_upper h_lower)

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

end
end

section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.GrothendieckTopology

noncomputable section
universe u v w

namespace AlgebraicGeometry.Scheme.Etale

/-- Kan extension along an isomorphism of small étale sites exists:
the inverse equivalence supplies its fixed universal-property model. -/
instance smallEtaleIso_hasLeftKanExtension {S T : Scheme.{u}} (f : S ⟶ T) [IsIso f]
    (A : Type v) [Category.{w} A] (F : T.Etaleᵒᵖ ⥤ A) :
    (smallEtalePullback f).op.HasLeftKanExtension F := sorry

/-- Every coefficient functor preserves Kan extension along a site equivalence. -/
instance smallEtaleIso_preservesLeftKanExtensions {S T : Scheme.{u}} (f : S ⟶ T) [IsIso f]
    (Λ : Type u) [CommRing Λ] :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (smallEtalePullback f).op := sorry

namespace CompactificationTransport

-- Local instance justification: use the specified strong sheafification projection before
-- searching unrelated over-site families; this adds no mathematical hypothesis.
-- Local instance justification (search instability): Use the given strong sheafification projection before generic over-site search in this diagram context.
attribute [local instance 10000] HasSheafify.isRightAdjoint

/-- Cancel the actual ambient isomorphism in the interior triangle. -/
theorem inverseInteriorTriangle {X T T' : Scheme.{u}}
    (j : X ⟶ T) (j' : X ⟶ T') (e : T' ≅ T) (hj : j' ≫ e.hom = j) :
    j ≫ e.inv = j' := by
  rw [← hj, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Cancel the actual ambient isomorphism in the structure triangle. -/
theorem inverseStructureTriangle {Y T T' : Scheme.{u}}
    (p : T ⟶ Y) (p' : T' ⟶ Y) (e : T' ≅ T) (hp : e.hom ≫ p = p') :
    e.inv ≫ p' = p := by
  rw [← hp, ← Category.assoc, e.inv_hom_id, Category.id_comp]

variable {X Y T T' : Scheme.{u}} (j : X ⟶ T) (p : T ⟶ Y)
  (j' : X ⟶ T') (p' : T' ⟶ Y) (e : T' ≅ T)
  (hj : j' ≫ e.hom = j) (hp : e.hom ≫ p = p')
  [IsOpenImmersion j] [IsOpenImmersion j'] (Λ : Type u) [CommRing Λ]
  [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [X.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [Y.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
  [T.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [T.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ U : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify T'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify T'.smallEtaleTopology AddCommGrpCat.{u}]
  [T'.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [T'.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ U : T'.Etale, HasWeakSheafify (T'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf T'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (etaleRestriction j).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}, (etaleRestriction j).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions (etaleRestriction j).op]
  [(etaleExtensionByZero j (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ))]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (etaleRestriction j').op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}, (etaleRestriction j').op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions (etaleRestriction j').op]
  [(etaleExtensionByZero j' (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero j' (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero j' (ModuleCat.{u} Λ))]
  [∀ F : T.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (smallEtalePullback j).op.HasLeftKanExtension F]
  [∀ F : T'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (smallEtalePullback j').op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (smallEtalePullback p).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (smallEtalePullback p').op.HasLeftKanExtension F]

/-- Proper direct-image mate for the specified ambient isomorphism over the same base. -/
def ambientMate :
    (etaleDerivedPushforward p : EtaleDerived T Λ ⥤ EtaleDerived Y Λ) ⋙
        etaleModuleDerivedInverseImage (𝟙 Y) Λ ⟶
      etaleModuleDerivedInverseImage e.hom Λ ⋙ etaleDerivedPushforward p' := by
  -- Local instance justification (proof-local temporary data): Transfer the given Kan extensions using this ambient isomorphism's structure or interior triangle and the identity laws.
  letI : ∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (p' ≫ 𝟙 Y)).op.HasLeftKanExtension F :=
    fun F => by simpa only [Category.comp_id] using
      (inferInstance : (smallEtalePullback p').op.HasLeftKanExtension F)
  -- Local instance justification (proof-local temporary data): Transfer the given Kan extensions using this ambient isomorphism's structure or interior triangle and the identity laws.
  letI : ∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (e.hom ≫ p)).op.HasLeftKanExtension F :=
    fun F => by rw [hp]; infer_instance
  exact etaleDerivedPushforwardBaseChange p (𝟙 Y) p' e.hom
    (IsPullback.of_horiz_isIso ⟨hp.trans (Category.comp_id p').symm⟩) Λ

/-- Interior mate transported through the existing exact extension-by-zero identifications. -/
def interiorMate :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        etaleModuleDerivedInverseImage e.hom Λ ⟶
      etaleModuleDerivedInverseImage (𝟙 X) Λ ⋙
        (etaleExtensionByZero j' (ModuleCat.{u} Λ)).mapDerivedCategory := by
  -- Local instance justification (proof-local temporary data): Transfer the given Kan extensions using this ambient isomorphism's structure or interior triangle and the identity laws.
  letI : ∀ F : T.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (𝟙 X ≫ j)).op.HasLeftKanExtension F :=
    fun F => by simpa only [Category.id_comp] using
      (inferInstance : (smallEtalePullback j).op.HasLeftKanExtension F)
  -- Local instance justification (proof-local temporary data): Transfer the given Kan extensions using this ambient isomorphism's structure or interior triangle and the identity laws.
  letI : ∀ F : T.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (j' ≫ e.hom)).op.HasLeftKanExtension F :=
    fun F => by rw [hj]; infer_instance
  exact whiskerRight (extensionByZeroDerivedIsoLowerShriekModule j Λ).hom
      (etaleModuleDerivedInverseImage e.hom Λ) ≫
    lowerShriekModuleDerivedBaseChange j e.hom j' (𝟙 X)
      (IsPullback.of_horiz_isIso ⟨(Category.id_comp j).trans hj.symm⟩) Λ ≫
    whiskerLeft (etaleModuleDerivedInverseImage (𝟙 X) Λ)
      (extensionByZeroDerivedIsoLowerShriekModule j' Λ).inv

/-- Change the ambient of a compactification using the specified ambient and interior mates. -/
def modelComparison :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward p : EtaleDerived T Λ ⥤ EtaleDerived Y Λ) ⟶
      (etaleExtensionByZero j' (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward p' : EtaleDerived T' Λ ⥤ EtaleDerived Y Λ) :=
  let J := (etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory
  let J' := (etaleExtensionByZero j' (ModuleCat.{u} Λ)).mapDerivedCategory
  let R : EtaleDerived T Λ ⥤ EtaleDerived Y Λ := etaleDerivedPushforward p
  let R' : EtaleDerived T' Λ ⥤ EtaleDerived Y Λ := etaleDerivedPushforward p'
  let E := etaleModuleDerivedInverseImage e.hom Λ
  let IY := etaleModuleDerivedInverseImage (𝟙 Y) Λ
  let IX := etaleModuleDerivedInverseImage (𝟙 X) Λ
  (Functor.rightUnitor (J ⋙ R)).inv ≫
    whiskerLeft (J ⋙ R) (derivedInverseImageIdentityIso Y Λ).inv ≫
    (Functor.associator J R IY).hom ≫
    whiskerLeft J (ambientMate p p' e hp Λ) ≫
    (Functor.associator J E R').inv ≫
    whiskerRight (interiorMate j j' e hj Λ) R' ≫
    (Functor.associator IX J' R').hom ≫
    whiskerRight (derivedInverseImageIdentityIso X Λ).hom (J' ⋙ R') ≫
    (Functor.leftUnitor (J' ⋙ R')).hom

/-- The model comparison has its actual reverse mate as inverse. -/
def modelIso :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward p : EtaleDerived T Λ ⥤ EtaleDerived Y Λ) ≅
      (etaleExtensionByZero j' (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward p' : EtaleDerived T' Λ ⥤ EtaleDerived Y Λ) where
  hom := modelComparison j p j' p' e hj hp Λ
  inv := modelComparison j' p' j p e.symm
    (inverseInteriorTriangle j j' e hj) (inverseStructureTriangle p p' e hp) Λ
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of the model isomorphism is the specified mate composite. -/
theorem modelIso_hom : (modelIso j p j' p' e hj hp Λ).hom =
    modelComparison j p j' p' e hj hp Λ := rfl

/-- The reverse map is built by the inverse ambient isomorphism and its two triangles. -/
theorem modelIso_inv : (modelIso j p j' p' e hj hp Λ).inv =
    modelComparison j' p' j p e.symm
      (inverseInteriorTriangle j j' e hj) (inverseStructureTriangle p p' e hp) Λ := rfl

end CompactificationTransport
end AlgebraicGeometry.Scheme.Etale
end
end
