module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Composition for cocontinuous morphisms of sites

This leaf contains the natural-isomorphism and composition API for cocontinuous
sheaf pushforwards. The basic pullback and topos-morphism construction remains
in `Topos.Cocontinuous`, so clients that do not need comparison isomorphisms
retain a narrower import. Equality-to-isomorphism wrappers for bundled topos
morphisms are deliberately not owned here: they would turn deferred equality
proofs into concrete inverse data.

Strictly commutative squares of continuous site functors use the short
`Functor.ContinuousSquare` namespace, whose pushforward comparison and
factorwise pullback mate are independent of a particular geometric setting.
-/

@[expose] public section

open CategoryTheory Opposite

universe t u1 u2 u3 u4 v1 v2 v3 v4

namespace CategoryTheory.Functor

variable {C : Type u1} [Category.{v1} C]
variable {D : Type u2} [Category.{v2} D]
variable {E : Type u3} [Category.{v3} E]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : GrothendieckTopology E)
variable (u : C ⥤ D) (v : D ⥤ E)
variable [Functor.IsCocontinuous u J K] [Functor.IsCocontinuous v K L]

section Pushforward

variable {A : Type t} [Category A]

/-- Cocontinuous sheaf pushforward along the identity functor is naturally isomorphic to
the identity on sheaves. -/
noncomputable def sheafPushforwardCocontinuousId (A : Type t) [Category A]
    (J : GrothendieckTopology C)
    [∀ P : Cᵒᵖ ⥤ A, (𝟭 C).op.HasPointwiseRightKanExtension P] :
    (𝟭 C).sheafPushforwardCocontinuous A J J ≅ 𝟭 (Sheaf J A) :=
  Functor.fullyFaithfulCancelRight (sheafToPresheaf J A)
    (((𝟭 C).sheafPushforwardCocontinuousCompSheafToPresheafIso A J J).trans
      ((NatIso.hcomp (Iso.refl (sheafToPresheaf J A))
          ((((𝟭 C).op.ranAdjunction A).ofNatIsoLeft
              (eqToIso Functor.whiskeringLeft_obj_id)).rightAdjointUniq
            (Adjunction.id : 𝟭 (Cᵒᵖ ⥤ A) ⊣ 𝟭 (Cᵒᵖ ⥤ A)))).trans
        (Functor.rightUnitor (sheafToPresheaf J A))))

variable [forall F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
variable [forall F : Dᵒᵖ ⥤ A, v.op.HasPointwiseRightKanExtension F]

/-- A natural isomorphism of cocontinuous functors induces an isomorphism of their sheaf
pushforward functors. -/
noncomputable def sheafPushforwardCocontinuousIso
    {u' : C ⥤ D} (e : u ≅ u')
    [u'.IsCocontinuous J K]
    [forall F : Cᵒᵖ ⥤ A, u'.op.HasPointwiseRightKanExtension F] :
    u.sheafPushforwardCocontinuous A J K ≅
      u'.sheafPushforwardCocontinuous A J K :=
  let ranIso :
      (u.op.ran : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) ≅
        (u'.op.ran : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) :=
    ((u.op.ranAdjunction A).ofNatIsoLeft
        ((whiskeringLeft _ _ _).mapIso (NatIso.op e.symm))).rightAdjointUniq
      (u'.op.ranAdjunction A)
  let uPush := u.sheafPushforwardCocontinuous A J K
  let u'Push := u'.sheafPushforwardCocontinuous A J K
  let presheafIso :
      uPush ⋙ sheafToPresheaf K A ≅
        u'Push ⋙ sheafToPresheaf K A :=
    calc
      uPush ⋙ sheafToPresheaf K A ≅ sheafToPresheaf J A ⋙ u.op.ran :=
        u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K
      _ ≅ sheafToPresheaf J A ⋙ u'.op.ran :=
        isoWhiskerLeft _ ranIso
      _ ≅ u'Push ⋙ sheafToPresheaf K A :=
        (u'.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm
  Functor.fullyFaithfulCancelRight (sheafToPresheaf K A) presheafIso

/-- The cocontinuous sheaf pushforward of a composite is canonically isomorphic to the composite
of the pushforwards. The composite cocontinuity instance is local, following Mathlib's analogous
continuous-pushforward API rather than adding a global composition instance. -/
noncomputable def sheafPushforwardCocontinuousComp
    [forall F : Cᵒᵖ ⥤ A, (u ⋙ v).op.HasPointwiseRightKanExtension F] :
    -- Local instance justification (instance diamond): the result is indexed by the displayed
    -- composite functor, so it must use this canonical composite cocontinuity witness rather
    -- than an unrelated ambient witness for the same functor.
    letI : Functor.IsCocontinuous (u ⋙ v) J L := isCocontinuous_comp u v J K
    u.sheafPushforwardCocontinuous A J K ⋙
      v.sheafPushforwardCocontinuous A K L ≅
        (u ⋙ v).sheafPushforwardCocontinuous A J L :=
  -- Local instance justification (instance diamond): keep construction of the comparison on
  -- the same composite cocontinuity witness that indexes its result type.
  letI : Functor.IsCocontinuous (u ⋙ v) J L := isCocontinuous_comp u v J K
  let uPush := u.sheafPushforwardCocontinuous A J K
  let vPush := v.sheafPushforwardCocontinuous A K L
  let uvPush := (u ⋙ v).sheafPushforwardCocontinuous A J L
  let ranCompIso :
      (u.op.ran : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) ⋙ (v.op.ran : (Dᵒᵖ ⥤ A) ⥤ Eᵒᵖ ⥤ A) ≅
        ((u ⋙ v).op.ran : (Cᵒᵖ ⥤ A) ⥤ Eᵒᵖ ⥤ A) :=
    (((v.op.ranAdjunction A).comp (u.op.ranAdjunction A)).ofNatIsoLeft
      (whiskeringLeftObjCompIso u.op v.op).symm).rightAdjointUniq
      ((u ⋙ v).op.ranAdjunction A)
  let presheafIso :
      (uPush ⋙ vPush) ⋙ sheafToPresheaf L A ≅
        uvPush ⋙ sheafToPresheaf L A :=
    calc
      (uPush ⋙ vPush) ⋙ sheafToPresheaf L A ≅
          uPush ⋙ (vPush ⋙ sheafToPresheaf L A) :=
        Functor.associator _ _ _
      _ ≅ uPush ⋙ (sheafToPresheaf K A ⋙ v.op.ran) :=
        isoWhiskerLeft _ (v.sheafPushforwardCocontinuousCompSheafToPresheafIso A K L)
      _ ≅ (uPush ⋙ sheafToPresheaf K A) ⋙ v.op.ran :=
        (Functor.associator _ _ _).symm
      _ ≅ (sheafToPresheaf J A ⋙ u.op.ran) ⋙ v.op.ran :=
        isoWhiskerRight (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K) _
      _ ≅ sheafToPresheaf J A ⋙ (u.op.ran ⋙ v.op.ran) :=
        Functor.associator _ _ _
      _ ≅ sheafToPresheaf J A ⋙ (u ⋙ v).op.ran :=
        isoWhiskerLeft _ ranCompIso
      _ ≅ uvPush ⋙ sheafToPresheaf L A :=
        (u ⋙ v).sheafPushforwardCocontinuousCompSheafToPresheafIso A J L |>.symm
  Functor.fullyFaithfulCancelRight (sheafToPresheaf L A) presheafIso

/-- If a composite is identified with a cocontinuous functor `uv`, the composite pushforward
identifies with the pushforward of `uv`. -/
noncomputable def sheafPushforwardCocontinuousComp'
    {uv : C ⥤ E} (euv : u ⋙ v ≅ uv)
    [uv.IsCocontinuous J L]
    [forall F : Cᵒᵖ ⥤ A, uv.op.HasPointwiseRightKanExtension F] :
    u.sheafPushforwardCocontinuous A J K ⋙
      v.sheafPushforwardCocontinuous A K L ≅
        uv.sheafPushforwardCocontinuous A J L :=
  -- Local instance justification (instance diamond): the intermediate composite comparison
  -- must use the canonical composite witness, independently of the witness attached to `uv`.
  letI : Functor.IsCocontinuous (u ⋙ v) J L := isCocontinuous_comp u v J K
  -- Local instance justification (instance diamond): transport the right-Kan data specifically
  -- across `euv`; an ambient instance for the definitionally equal composite need not be the
  -- transported datum used by this comparison.
  letI : forall F : Cᵒᵖ ⥤ A, (u ⋙ v).op.HasPointwiseRightKanExtension F :=
    fun F => HasPointwiseRightKanExtension.of_iso (NatIso.op euv) (Iso.refl F)
  sheafPushforwardCocontinuousComp J K L u v ≪≫
    sheafPushforwardCocontinuousIso J L (u ⋙ v) euv

end Pushforward

section Pullback

variable {A : Type t} [Category A]
variable [Functor.IsContinuous u J K] [Functor.IsContinuous v K L]
variable [forall F : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension F]
variable [forall F : Dᵒᵖ ⥤ A, v.op.HasLeftKanExtension F]
variable [HasWeakSheafify K A] [HasWeakSheafify L A]

/-- The sheaf pullback attached to a composite of continuous functors is canonically the composite
of the corresponding sheaf pullbacks. -/
noncomputable def sheafPullbackComp'
    {uv : C ⥤ E} (euv : u ⋙ v ≅ uv)
    [Functor.IsContinuous uv J L]
    [forall F : Cᵒᵖ ⥤ A, uv.op.HasLeftKanExtension F] :
    u.sheafPullback A J K ⋙ v.sheafPullback A K L ≅
      uv.sheafPullback A J L :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        (u.sheafAdjunctionContinuous A J K)
        (v.sheafAdjunctionContinuous A K L)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp' euv A J K L))
    (uv.sheafAdjunctionContinuous A J L)

end Pullback

namespace ContinuousSquare

variable {C' : Type u1} [Category.{v1} C']
variable {C : Type u2} [Category.{v2} C]
variable {D' : Type u3} [Category.{v3} D']
variable {D : Type u4} [Category.{v4} D]

variable {J' : GrothendieckTopology C'} {J : GrothendieckTopology C}
variable {K' : GrothendieckTopology D'} {K : GrothendieckTopology D}

variable {u' : D' ⥤ C'} {u : D ⥤ C} {v' : C' ⥤ C} {v : D' ⥤ D}

variable [Functor.IsContinuous u K J] [Functor.IsContinuous u' K' J']
variable [Functor.IsContinuous v K' K] [Functor.IsContinuous v' J' J]

/-- A strictly commutative square of continuous site functors induces the canonical comparison
between the two composites of sheaf pushforwards. -/
@[stacks 0FN7 "continuous-square pushforward comparison"]
noncomputable def pushforwardIso (A : Type t) [Category A]
    (hcomm : v ⋙ u = u' ⋙ v') :
    v'.sheafPushforwardContinuous A J' J ⋙
        u'.sheafPushforwardContinuous A K' J' ≅
      u.sheafPushforwardContinuous A K J ⋙
        v.sheafPushforwardContinuous A K' K :=
  -- Local instance justification (defeq pin): pin continuity of `v ⋙ u` to `Functor.isContinuous_comp v u K' K J` so transport along `hcomm.symm` in `sheafPushforwardContinuousComp'` matches the composite comparison on the right.
  letI : Functor.IsContinuous (v ⋙ u) K' J :=
    Functor.isContinuous_comp v u K' K J
  (Functor.sheafPushforwardContinuousComp'
    (eqToIso hcomm.symm) A K' J' J) ≪≫
      (Functor.sheafPushforwardContinuousComp v u A K' K J).symm

section Pullback

/-- The factorwise left-adjoint mate of `pushforwardIso`, expressed as a comparison between
the corresponding composites of sheaf pullbacks. -/
@[stacks 0FN7 "continuous-square pullback comparison"]
noncomputable def pullbackIso (A : Type t) [Category A]
    [∀ P : Dᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [∀ P : D'ᵒᵖ ⥤ A, u'.op.HasLeftKanExtension P]
    [∀ P : D'ᵒᵖ ⥤ A, v.op.HasLeftKanExtension P]
    [∀ P : C'ᵒᵖ ⥤ A, v'.op.HasLeftKanExtension P]
    [HasWeakSheafify J A] [HasWeakSheafify J' A] [HasWeakSheafify K A]
    (hcomm : v ⋙ u = u' ⋙ v') :
    u'.sheafPullback A K' J' ⋙ v'.sheafPullback A J' J ≅
      v.sheafPullback A K' K ⋙ u.sheafPullback A K J :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        (u'.sheafAdjunctionContinuous A K' J')
        (v'.sheafAdjunctionContinuous A J' J)).ofNatIsoRight
      (pushforwardIso (u := u) (u' := u') (v := v) (v' := v') A hcomm))
    (Adjunction.comp
      (v.sheafAdjunctionContinuous A K' K)
      (u.sheafAdjunctionContinuous A K J))

end Pullback

end ContinuousSquare

end CategoryTheory.Functor
