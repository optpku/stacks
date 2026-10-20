/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Transitivity
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AtlasDescent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Differentials

/-!
# Étale descent of relative differentials

Relative differentials descend from an étale atlas. They can be presented by scheme
relative differentials when the target is a scheme, by the transitivity cokernel for
an arbitrary target, or by relative differentials in an étale-vertical presentation square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite ConcreteCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QCoh
open scoped AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Differentials

variable {S : Scheme.{u}}

/-- The morphism of schemes over `S` recovered from `φ ≫ f : ofOver U ⟶ ofOver Y`. -/
def atlasOver {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) : U ⟶ Y :=
  Yoneda.fullyFaithful.preimage (φ ≫ f : yoneda.obj U ⟶ yoneda.obj Y)

/-- The atlas morphism to the target scheme is the Yoneda preimage of `φ ≫ f`. -/
theorem atlasOver_eq {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) :
    atlasOver f φ = Yoneda.fullyFaithful.preimage (φ ≫ f : yoneda.obj U ⟶ yoneda.obj Y) :=
  rfl

/-- The sheaf `Ω_{U/Y}` on the underlying scheme of an étale atlas. -/
def atlasModule {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) : Scheme.QCoh U.left :=
  ⟨Ω[(atlasOver f φ).left.toShHom], isQuasicoherent_differentials (atlasOver f φ).left⟩

/-- `atlasModule` packs the scheme-level sheaf of differentials of `U ⟶ Y`. -/
theorem atlasModule_eq {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) :
    (atlasModule f φ).obj = Ω[(atlasOver f φ).left.toShHom] :=
  rfl

/-- Quasi-coherence of the Zariski module underlying `atlasModule`. -/
instance atlasModule_isQuasicoherent {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) :
    ((atlasModule f φ).obj).IsQuasicoherent :=
  (atlasModule f φ).property

/-- The scheme morphism `R ⟶ Y` obtained from the source kernel-pair projection. -/
def relationOver {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (atlasGroupoid φ).R.left ⟶ Y.left :=
  (atlasGroupoid φ).s.left ≫ (atlasOver f φ).left

/-- `relationOver` is `s.left ≫ (atlasOver f φ).left`. -/
theorem relationOver_eq {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    relationOver f φ = (atlasGroupoid φ).s.left ≫ (atlasOver f φ).left :=
  rfl

/-- The two kernel-pair projections equalize `U ⟶ Y`. -/
theorem relationOver_t {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (atlasGroupoid φ).t.left ≫ (atlasOver f φ).left = relationOver f φ :=
  sorry

/-- The sheaf `Ω_{R/Y}` on the arrow scheme of the atlas groupoid. -/
def relationModule {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    Scheme.QCoh (atlasGroupoid φ).R.left :=
  ⟨Ω[(relationOver f φ).toShHom], isQuasicoherent_differentials (relationOver f φ)⟩

/-- `relationModule` packs the scheme-level sheaf of differentials of `R ⟶ Y`. -/
theorem relationModule_eq {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (relationModule f φ).obj = Ω[(relationOver f φ).toShHom] :=
  rfl

/-- The source comparison `s* Ω_{U/Y} ⟶ Ω_{R/Y}`. -/
def sourceComparison {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).obj (atlasModule f φ) ⟶
      relationModule f φ :=
  homMk (RingedSpace.Hom.Differentials.Transitivity.baseChange
      (atlasGroupoid φ).s.left.toShHom (atlasOver f φ).left.toShHom)

/-- `sourceComparison` is the transitivity base-change map of `s` along `U ⟶ Y`. -/
theorem sourceComparison_eq {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    sourceComparison f φ =
      homMk (RingedSpace.Hom.Differentials.Transitivity.baseChange
          (atlasGroupoid φ).s.left.toShHom (atlasOver f φ).left.toShHom) :=
  rfl

/-- The source comparison is an isomorphism because `s` is étale. -/
instance sourceComparison_isIso {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    IsIso (sourceComparison f φ) :=
  sorry

/-- The scheme morphism `R ⟶ Y` obtained from the target kernel-pair projection. -/
def targetRelationOver {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (atlasGroupoid φ).R.left ⟶ Y.left :=
  (atlasGroupoid φ).t.left ≫ (atlasOver f φ).left

/-- `targetRelationOver` is `t.left ≫ (atlasOver f φ).left`. -/
theorem targetRelationOver_eq {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    targetRelationOver f φ = (atlasGroupoid φ).t.left ≫ (atlasOver f φ).left :=
  rfl

/-- The sheaf `Ω_{R/Y}` formed using the target kernel-pair projection. -/
def targetRelationModule {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    Scheme.QCoh (atlasGroupoid φ).R.left :=
  ⟨Ω[(targetRelationOver f φ).toShHom], isQuasicoherent_differentials (targetRelationOver f φ)⟩

/-- `targetRelationModule` packs the scheme-level sheaf of differentials of `t ≫ (U ⟶ Y)`. -/
theorem targetRelationModule_eq {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (targetRelationModule f φ).obj = Ω[(targetRelationOver f φ).toShHom] :=
  rfl

/-- Identification of the two presentations of `Ω_{R/Y}`, as a consequence of the
kernel-pair equalization `ofOverMap t ≫ φ = ofOverMap s ≫ φ`. -/
theorem omega_relationOver_t {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    targetRelationModule f φ = relationModule f φ :=
  sorry

/-- The target comparison `t* Ω_{U/Y} ⟶ Ω[(t ≫ (U ⟶ Y))]`. -/
def targetComparison {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).obj (atlasModule f φ) ⟶
      targetRelationModule f φ :=
  homMk (RingedSpace.Hom.Differentials.Transitivity.baseChange
      (atlasGroupoid φ).t.left.toShHom (atlasOver f φ).left.toShHom)

/-- `targetComparison` is the transitivity base-change map of `t` along `U ⟶ Y`. -/
theorem targetComparison_eq {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    targetComparison f φ =
      homMk (RingedSpace.Hom.Differentials.Transitivity.baseChange
          (atlasGroupoid φ).t.left.toShHom (atlasOver f φ).left.toShHom) :=
  rfl

/-- The target comparison is an isomorphism because `t` is étale. -/
instance targetComparison_isIso {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    IsIso (targetComparison f φ) :=
  sorry

/-- The descent isomorphism `α : s* Ω_{U/Y} ⟶ t* Ω_{U/Y}` obtained by composing the
two legs after identifying the two presentations of
`Ω_{R/Y}` along `ofOverMap t ≫ φ = ofOverMap s ≫ φ`. -/
def descentIso {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).obj (atlasModule f φ) ⟶
      (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).obj (atlasModule f φ) :=
  sourceComparison f φ ≫
    eqToHom (omega_relationOver_t f φ).symm ≫ inv (targetComparison f φ)

/-- `descentIso` is `sourceComparison ≫ inv targetComparison` after identifying the
two presentations of `Ω_{R/Y}`. -/
theorem descentIso_spec {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    descentIso f φ =
      sourceComparison f φ ≫
        eqToHom (omega_relationOver_t f φ).symm ≫ inv (targetComparison f φ) :=
  rfl

/-- The descent isomorphism `α` is an isomorphism. -/
instance descentIso_isIso {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    IsIso (descentIso f φ) :=
  sorry

/-- The groupoid action `t* Ω_{U/Y} ⟶ s* Ω_{U/Y}` opposite to the displayed
isomorphism `α`. -/
def descentAction {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).obj (atlasModule f φ) ⟶
      (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).obj (atlasModule f φ) :=
  inv (descentIso f φ)

/-- `descentAction` is the inverse of `descentIso`. -/
theorem descentAction_eq {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    descentAction f φ = inv (descentIso f φ) :=
  rfl

/-- The groupoid action of `Ω_{U/Y}` satisfies the cocycle condition. -/
theorem descentAction_cocycle {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    GroupoidScheme.Cocycle (atlasGroupoid φ) (atlasModule f φ) (descentAction f φ) :=
  sorry

/-- The groupoid action of `Ω_{U/Y}` satisfies the unit condition. -/
theorem descentAction_unit {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    GroupoidScheme.Unit (atlasGroupoid φ) (atlasModule f φ) (descentAction f φ) :=
  sorry

/-- The equivariant quasi-coherent module `(Ω_{U/Y}, α)` on the étale atlas groupoid. -/
def descentSystem {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] : (atlasGroupoid φ).QCoh :=
  GroupoidScheme.QCoh.of (atlasModule f φ) (descentAction f φ)
    (descentAction_cocycle f φ) (descentAction_unit f φ)

/-- The underlying module of `descentSystem` is `atlasModule`. -/
theorem descentSystem_obj {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    GroupoidScheme.QCoh.obj (descentSystem f φ) = atlasModule f φ :=
  rfl

/-- The equivariance map of `descentSystem` is `descentAction`. -/
theorem descentSystem_action {X : AlgebraicSpace S} {U Y : Over S}
    (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X) [Etale φ] :
    GroupoidScheme.QCoh.action (descentSystem f φ) = descentAction f φ :=
  sorry

/-- The sheaf on `X` obtained by glueing `Ω_{U/Y}` along the étale atlas groupoid. -/
def glued {X : AlgebraicSpace S} {U Y : Over S} (f : X ⟶ ofOver Y)
    (φ : ofOver U ⟶ X) [Etale φ]
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ] : QCoh X :=
  (toGroupoid φ).inv.obj (descentSystem f φ)

/-- `glued` is the inverse image of `descentSystem` under the atlas descent equivalence. -/
theorem glued_eq {X : AlgebraicSpace S} {U Y : Over S} (f : X ⟶ ofOver Y)
    (φ : ofOver U ⟶ X) [Etale φ]
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ] :
    glued f φ = (toGroupoid φ).inv.obj (descentSystem f φ) :=
  rfl

/-- Restricting the glued sheaf along the atlas recovers the descent system. -/
def glued_counit {X : AlgebraicSpace S} {U Y : Over S} (f : X ⟶ ofOver Y)
    (φ : ofOver U ⟶ X) [Etale φ]
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ] :
    (toGroupoid φ).obj (glued f φ) ≅ descentSystem f φ :=
  (toGroupoid φ).asEquivalence.counitIso.app (descentSystem f φ)

/-- The sheaf `Ω_{U/V}` on the underlying scheme of `U`. -/
def diagramModule {U V : Over S} (ψ : U ⟶ V) : Scheme.QCoh U.left :=
  ⟨Ω[ψ.left.toShHom], isQuasicoherent_differentials ψ.left⟩

/-- `diagramModule` packs the scheme-level sheaf of differentials of `ψ`. -/
theorem diagramModule_eq {U V : Over S} (ψ : U ⟶ V) :
    (diagramModule ψ).obj = Ω[ψ.left.toShHom] :=
  rfl

/-- The canonical sheaf `Ω[h]` packed as a quasi-coherent module. -/
def packedRelativeDifferentials {X Y : AlgebraicSpace S} (h : X ⟶ Y) : QCoh X :=
  ⟨relativeDifferentials h, isQuasicoherent_relativeDifferentials h⟩

/-- `packedRelativeDifferentials` packs `relativeDifferentials`. -/
theorem packedRelativeDifferentials_obj {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    (packedRelativeDifferentials h).obj = relativeDifferentials h :=
  rfl

/-- The sheaf `Ω_{U/V}` as a quasi-coherent module on `ofOver U`. -/
def diagramPacked {U V : Over S} (ψ : U ⟶ V) : QCoh (ofOver U) :=
  packedRelativeDifferentials (ofOverMap ψ)

/-- `diagramPacked` packs `Ω[ofOverMap ψ]`. -/
theorem diagramPacked_obj {U V : Over S} (ψ : U ⟶ V) :
    (diagramPacked ψ).obj = relativeDifferentials (ofOverMap ψ) :=
  rfl

/-- Zariski restriction of the algebraic-space sheaf `Ω_{U/V}`. -/
def diagramAtlasModule {U V : Over S} (ψ : U ⟶ V) : Scheme.QCoh U.left :=
  (restrictToScheme U).obj (diagramPacked ψ)

/-- `diagramAtlasModule` is `restrictToScheme` of `diagramPacked`. -/
theorem diagramAtlasModule_eq {U V : Over S} (ψ : U ⟶ V) :
    diagramAtlasModule ψ = (restrictToScheme U).obj (diagramPacked ψ) :=
  rfl

/-- The Zariski restriction of relative differentials of a morphism of represented schemes
is isomorphic to its usual scheme differential module. -/
theorem diagramAtlasModule_isIsomorphic_diagramModule {U V : Over S} (ψ : U ⟶ V) :
    IsIsomorphic (diagramAtlasModule ψ) (diagramModule ψ) :=
  sorry

/-- The comparison `a* Ω[f] ⟶ Ω_{U/V}` of a commutative presentation square. -/
def diagramComparison {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    (sq : CommSq a (ofOverMap ψ) f b) :
    (Modules.pullback a).obj (relativeDifferentials f) ⟶
      relativeDifferentials (ofOverMap ψ) :=
  comparison a b f (ofOverMap ψ) sq.w

/-- `diagramComparison` is the differential comparison of the commutative presentation square. -/
theorem diagramComparison_eq {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    (sq : CommSq a (ofOverMap ψ) f b) :
    diagramComparison f ψ a b sq =
      comparison a b f (ofOverMap ψ) sq.w :=
  rfl

/-- The comparison for an étale-vertical presentation square is an isomorphism. -/
instance diagramComparison_isIso {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b) :
    IsIso (diagramComparison f ψ a b sq) :=
  sorry

/-- The comparison for an étale-vertical presentation square as a morphism of quasi-coherent modules. -/
def diagramComparisonQCoh {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    (sq : CommSq a (ofOverMap ψ) f b) :
    (QCoh.pullback a).obj (packedRelativeDifferentials f) ⟶ diagramPacked ψ :=
  homMk (eqToHom (QCoh.pullback_obj a (packedRelativeDifferentials f)) ≫
    diagramComparison f ψ a b sq)

/-- The comparison for an étale-vertical presentation square after restriction to the underlying scheme of `U`. -/
def diagramComparisonScheme {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    (sq : CommSq a (ofOverMap ψ) f b) :
    (restrictToScheme U).obj ((QCoh.pullback a).obj (packedRelativeDifferentials f)) ⟶
      diagramAtlasModule ψ :=
  (restrictToScheme U).map (diagramComparisonQCoh f ψ a b sq)

/-- The restricted comparison for an étale-vertical presentation square is an isomorphism. -/
instance diagramComparisonScheme_isIso {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b) :
    IsIso (diagramComparisonScheme f ψ a b sq) :=
  sorry

/-- The groupoid action on `Ω_{U/V}` obtained by conjugating the kernel-pair
identification of pullbacks of `Ω[f]` by the canonical differential comparison. -/
def diagramDescentAction {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b) :
    (Scheme.QCoh.pullback (atlasGroupoid a).t.left).obj (diagramAtlasModule ψ) ⟶
      (Scheme.QCoh.pullback (atlasGroupoid a).s.left).obj (diagramAtlasModule ψ) :=
  (Scheme.QCoh.pullback (atlasGroupoid a).t.left).map
      (inv (diagramComparisonScheme f ψ a b sq)
        (I := inferInstanceAs (IsIso (diagramComparisonScheme f ψ a b sq)))) ≫
    QCoh.action a (packedRelativeDifferentials f) ≫
    (Scheme.QCoh.pullback (atlasGroupoid a).s.left).map
      (diagramComparisonScheme f ψ a b sq)

/-- The conjugated kernel-pair action on `Ω_{U/V}` is an isomorphism. -/
instance diagramDescentAction_isIso {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b) :
    IsIso (diagramDescentAction f ψ a b sq) :=
  sorry

/-- The descent isomorphism `s* Ω_{U/V} ⟶ t* Ω_{U/V}` opposite to the conjugated
kernel-pair action. -/
def diagramDescentIso {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b) :
    (Scheme.QCoh.pullback (atlasGroupoid a).s.left).obj (diagramAtlasModule ψ) ⟶
      (Scheme.QCoh.pullback (atlasGroupoid a).t.left).obj (diagramAtlasModule ψ) :=
  inv (diagramDescentAction f ψ a b sq)

/-- The descent isomorphism of `Ω_{U/V}` is an isomorphism. -/
instance diagramDescentIso_isIso {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b) :
    IsIso (diagramDescentIso f ψ a b sq) :=
  sorry

/-- The action on `Ω_{U/V}` satisfies the cocycle condition. -/
theorem diagramDescentAction_cocycle {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b) :
    GroupoidScheme.Cocycle (atlasGroupoid a) (diagramAtlasModule ψ)
      (diagramDescentAction f ψ a b sq) :=
  sorry

/-- The action on `Ω_{U/V}` satisfies the unit condition. -/
theorem diagramDescentAction_unit {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b) :
    GroupoidScheme.Unit (atlasGroupoid a) (diagramAtlasModule ψ)
      (diagramDescentAction f ψ a b sq) :=
  sorry

/-- The equivariant module `Ω_{U/V}` on the atlas groupoid of `a`. -/
def diagramDescentSystem {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b) : (atlasGroupoid a).QCoh :=
  GroupoidScheme.QCoh.of (diagramAtlasModule ψ) (diagramDescentAction f ψ a b sq)
    (diagramDescentAction_cocycle f ψ a b sq) (diagramDescentAction_unit f ψ a b sq)

/-- The sheaf on `X` obtained by glueing `Ω_{U/V}` along the étale atlas groupoid of `a`,
using the commutative presentation square to identify `s* Ω_{U/V}` with `t* Ω_{U/V}`. -/
def diagramGlued {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b)
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a] : QCoh X :=
  (toGroupoid a).inv.obj (diagramDescentSystem f ψ a b sq)

/-- `diagramGlued` is the inverse image of `diagramDescentSystem` under the atlas descent
equivalence. -/
theorem diagramGlued_eq {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b)
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a] :
    diagramGlued f ψ a b sq = (toGroupoid a).inv.obj (diagramDescentSystem f ψ a b sq) :=
  rfl

/-- The square identifying `(U ⟶ Y) ≫ (Y ⟶ S)` with the unique map to `S`. -/
theorem cokerComparison_sq {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) :
    (φ ≫ f) ≫ SchemeRealization.toBase Y = SchemeRealization.toBase (ofOver U) ≫ 𝟙 (ofOver (Over.mk (𝟙 S))) :=
  sorry

/-- The comparison `(U ⟶ Y)* Ω_{Y/S} ⟶ Ω_{U/S}`. -/
def cokerComparison {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) :
    (Modules.pullback (φ ≫ f)).obj (relativeDifferentials (SchemeRealization.toBase Y)) ⟶
      relativeDifferentials (SchemeRealization.toBase (ofOver U)) :=
  comparison (φ ≫ f) (𝟙 (ofOver (Over.mk (𝟙 S)))) (SchemeRealization.toBase Y) (SchemeRealization.toBase (ofOver U))
    (cokerComparison_sq f φ)

/-- `cokerComparison` is the differential comparison of `U ⟶ Y` along `Y ⟶ S`. -/
theorem cokerComparison_eq {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) :
    cokerComparison f φ =
      comparison (φ ≫ f) (𝟙 (ofOver (Over.mk (𝟙 S)))) (SchemeRealization.toBase Y)
        (SchemeRealization.toBase (ofOver U)) (cokerComparison_sq f φ) :=
  rfl

/-- The sheaf `Ω_{U/Y}` as the cokernel of `(U ⟶ Y)* Ω_{Y/S} ⟶ Ω_{U/S}`. -/
def cokerModule {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) : (ofOver U).Modules :=
  cokernel (cokerComparison f φ)

/-- The underlying module of `cokerModule` is the displayed cokernel. -/
theorem cokerModule_eq {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) :
    cokerModule f φ = cokernel (cokerComparison f φ) :=
  rfl

/-- Quasi-coherence of the cokernel presentation of `Ω_{U/Y}`. -/
instance cokerModule_isQuasicoherent {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) :
    (cokerModule f φ).IsQuasicoherent :=
  sorry

/-- The cokernel projection `Ω_{U/S} ⟶ cokerModule`. -/
def cokerModule_π {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) :
    relativeDifferentials (SchemeRealization.toBase (ofOver U)) ⟶ cokerModule f φ :=
  cokernel.π (cokerComparison f φ)

/-- The comparison `(U ⟶ Y)* Ω_{Y/S} ⟶ Ω_{U/S}` followed by the cokernel
projection is zero. -/
theorem cokerModule_spec {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) :
    cokerComparison f φ ≫ cokerModule_π f φ = 0 :=
  cokernel.condition _

/-- The cokernel presentation of `Ω_{U/Y}` as a quasi-coherent module on `ofOver U`. -/
def cokerPacked {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) : QCoh (ofOver U) :=
  ⟨cokerModule f φ, cokerModule_isQuasicoherent f φ⟩

/-- `cokerPacked` packs `cokerModule`. -/
theorem cokerPacked_obj {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) :
    (cokerPacked f φ).obj = cokerModule f φ :=
  rfl

/-- The Zariski restriction of the cokernel presentation of `Ω_{U/Y}`. -/
def cokerAtlasModule {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) : Scheme.QCoh U.left :=
  (restrictToScheme U).obj (cokerPacked f φ)

/-- `cokerAtlasModule` is `restrictToScheme` of `cokerPacked`. -/
theorem cokerAtlasModule_eq {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) :
    cokerAtlasModule f φ = (restrictToScheme U).obj (cokerPacked f φ) :=
  rfl

/-- The morphism `R ⟶ Y` obtained from the source kernel-pair projection. -/
def cokerRelationHom {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    ofOver (atlasGroupoid φ).R ⟶ Y :=
  ofOverMap (atlasGroupoid φ).s ≫ φ ≫ f

/-- `cokerRelationHom` is `ofOverMap s ≫ φ ≫ f`. -/
theorem cokerRelationHom_eq {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    cokerRelationHom f φ = ofOverMap (atlasGroupoid φ).s ≫ φ ≫ f :=
  rfl

/-- The square identifying `(R ⟶ Y) ≫ (Y ⟶ S)` with the unique map to `S`. -/
theorem cokerRelationComparison_sq {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    cokerRelationHom f φ ≫ SchemeRealization.toBase Y =
      SchemeRealization.toBase (ofOver (atlasGroupoid φ).R) ≫ 𝟙 (ofOver (Over.mk (𝟙 S))) :=
  sorry

/-- The comparison `(R ⟶ Y)* Ω_{Y/S} ⟶ Ω_{R/S}`. -/
def cokerRelationComparison {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Modules.pullback (cokerRelationHom f φ)).obj (relativeDifferentials (SchemeRealization.toBase Y)) ⟶
      relativeDifferentials (SchemeRealization.toBase (ofOver (atlasGroupoid φ).R)) :=
  comparison (cokerRelationHom f φ) (𝟙 (ofOver (Over.mk (𝟙 S)))) (SchemeRealization.toBase Y)
    (SchemeRealization.toBase (ofOver (atlasGroupoid φ).R)) (cokerRelationComparison_sq f φ)

/-- The sheaf `Ω_{R/Y}` as the cokernel of `(R ⟶ Y)* Ω_{Y/S} ⟶ Ω_{R/S}`. -/
def cokerRelationModule {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (ofOver (atlasGroupoid φ).R).Modules :=
  cokernel (cokerRelationComparison f φ)

/-- Quasi-coherence of the cokernel presentation of `Ω_{R/Y}`. -/
instance cokerRelationModule_isQuasicoherent {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (cokerRelationModule f φ).IsQuasicoherent :=
  sorry

/-- The cokernel presentation of `Ω_{R/Y}` as a quasi-coherent module on `R`. -/
def cokerRelationPacked {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    QCoh (ofOver (atlasGroupoid φ).R) :=
  ⟨cokerRelationModule f φ, cokerRelationModule_isQuasicoherent f φ⟩

/-- The Zariski restriction of the cokernel presentation of `Ω_{R/Y}`. -/
def cokerRelationAtlas {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    Scheme.QCoh (atlasGroupoid φ).R.left :=
  (restrictToScheme (atlasGroupoid φ).R).obj (cokerRelationPacked f φ)

/-- The square identifying `s ≫ (U ⟶ S)` with the unique map `R ⟶ S`. -/
theorem cokerPullbackBase_sq {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    ofOverMap (atlasGroupoid φ).s ≫ SchemeRealization.toBase (ofOver U) =
      SchemeRealization.toBase (ofOver (atlasGroupoid φ).R) ≫ 𝟙 (ofOver (Over.mk (𝟙 S))) :=
  sorry

/-- The comparison `s* Ω_{U/S} ⟶ Ω_{R/S}` along the source kernel-pair projection. -/
def cokerPullbackBase {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Modules.pullback (ofOverMap (atlasGroupoid φ).s)).obj
        (relativeDifferentials (SchemeRealization.toBase (ofOver U))) ⟶
      relativeDifferentials (SchemeRealization.toBase (ofOver (atlasGroupoid φ).R)) :=
  comparison (ofOverMap (atlasGroupoid φ).s) (𝟙 (ofOver (Over.mk (𝟙 S))))
    (SchemeRealization.toBase (ofOver U)) (SchemeRealization.toBase (ofOver (atlasGroupoid φ).R))
    (cokerPullbackBase_sq f φ)

/-- The pulled comparison `(pullback s).map cokerComparison` followed by
`cokerPullbackBase ≫ cokernel.π` is zero. -/
theorem cokerSourceModules_zero {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Modules.pullback (ofOverMap (atlasGroupoid φ).s)).map (cokerComparison f φ) ≫
        cokerPullbackBase f φ ≫ cokernel.π (cokerRelationComparison f φ) = 0 :=
  sorry

/-- The source comparison `s* Ω_{U/Y} ⟶ Ω_{R/Y}` of the cokernel presentation. -/
def cokerSourceModules {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Modules.pullback (ofOverMap (atlasGroupoid φ).s)).obj (cokerModule f φ) ⟶
      cokerRelationModule f φ :=
  inv (cokernelComparison (cokerComparison f φ)
      (Modules.pullback (ofOverMap (atlasGroupoid φ).s)))
    (I := inferInstanceAs (IsIso (cokernelComparison (cokerComparison f φ)
      (Modules.pullback (ofOverMap (atlasGroupoid φ).s))))) ≫
    cokernel.desc
      ((Modules.pullback (ofOverMap (atlasGroupoid φ).s)).map (cokerComparison f φ))
      (cokerPullbackBase f φ ≫ cokernel.π (cokerRelationComparison f φ))
      (cokerSourceModules_zero f φ)

/-- The source comparison of the packed cokernel modules. -/
def cokerSourceQCoh {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (QCoh.pullback (ofOverMap (atlasGroupoid φ).s)).obj (cokerPacked f φ) ⟶
      cokerRelationPacked f φ :=
  homMk (eqToHom (QCoh.pullback_obj (ofOverMap (atlasGroupoid φ).s) (cokerPacked f φ)) ≫
    cokerSourceModules f φ)

/-- The source comparison `s* Ω_{U/Y} ⟶ Ω_{R/Y}` after restriction to schemes. -/
def cokerSourceComparison {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).obj (cokerAtlasModule f φ) ⟶
      cokerRelationAtlas f φ :=
  (restrictPullbackIso (atlasGroupoid φ).s).inv.app (cokerPacked f φ) ≫
    (restrictToScheme (atlasGroupoid φ).R).map (cokerSourceQCoh f φ)

/-- The source comparison of the cokernel presentation is an isomorphism. -/
instance cokerSourceComparison_isIso {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    IsIso (cokerSourceComparison f φ) :=
  sorry

/-- The square identifying `t ≫ (U ⟶ S)` with the unique map `R ⟶ S`. -/
theorem cokerPullbackBase_t_sq {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    ofOverMap (atlasGroupoid φ).t ≫ SchemeRealization.toBase (ofOver U) =
      SchemeRealization.toBase (ofOver (atlasGroupoid φ).R) ≫ 𝟙 (ofOver (Over.mk (𝟙 S))) :=
  sorry

/-- The comparison `t* Ω_{U/S} ⟶ Ω_{R/S}` along the target kernel-pair projection. -/
def cokerPullbackBase_t {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Modules.pullback (ofOverMap (atlasGroupoid φ).t)).obj
        (relativeDifferentials (SchemeRealization.toBase (ofOver U))) ⟶
      relativeDifferentials (SchemeRealization.toBase (ofOver (atlasGroupoid φ).R)) :=
  comparison (ofOverMap (atlasGroupoid φ).t) (𝟙 (ofOver (Over.mk (𝟙 S))))
    (SchemeRealization.toBase (ofOver U)) (SchemeRealization.toBase (ofOver (atlasGroupoid φ).R))
    (cokerPullbackBase_t_sq f φ)

/-- The pulled comparison along `t` followed by `cokerPullbackBase_t ≫ cokernel.π`
is zero. -/
theorem cokerTargetModules_zero {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Modules.pullback (ofOverMap (atlasGroupoid φ).t)).map (cokerComparison f φ) ≫
        cokerPullbackBase_t f φ ≫ cokernel.π (cokerRelationComparison f φ) = 0 :=
  sorry

/-- The target comparison `t* Ω_{U/Y} ⟶ Ω_{R/Y}` of the cokernel presentation. -/
def cokerTargetModules {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Modules.pullback (ofOverMap (atlasGroupoid φ).t)).obj (cokerModule f φ) ⟶
      cokerRelationModule f φ :=
  inv (cokernelComparison (cokerComparison f φ)
      (Modules.pullback (ofOverMap (atlasGroupoid φ).t)))
    (I := inferInstanceAs (IsIso (cokernelComparison (cokerComparison f φ)
      (Modules.pullback (ofOverMap (atlasGroupoid φ).t))))) ≫
    cokernel.desc
      ((Modules.pullback (ofOverMap (atlasGroupoid φ).t)).map (cokerComparison f φ))
      (cokerPullbackBase_t f φ ≫ cokernel.π (cokerRelationComparison f φ))
      (cokerTargetModules_zero f φ)

/-- The target comparison of the packed cokernel modules. -/
def cokerTargetQCoh {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (QCoh.pullback (ofOverMap (atlasGroupoid φ).t)).obj (cokerPacked f φ) ⟶
      cokerRelationPacked f φ :=
  homMk (eqToHom (QCoh.pullback_obj (ofOverMap (atlasGroupoid φ).t) (cokerPacked f φ)) ≫
    cokerTargetModules f φ)

/-- The target comparison `t* Ω_{U/Y} ⟶ Ω_{R/Y}` after restriction to schemes. -/
def cokerTargetComparison {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).obj (cokerAtlasModule f φ) ⟶
      cokerRelationAtlas f φ :=
  (restrictPullbackIso (atlasGroupoid φ).t).inv.app (cokerPacked f φ) ≫
    (restrictToScheme (atlasGroupoid φ).R).map (cokerTargetQCoh f φ)

/-- The target comparison of the cokernel presentation is an isomorphism. -/
instance cokerTargetComparison_isIso {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    IsIso (cokerTargetComparison f φ) :=
  sorry

/-- The descent isomorphism of the cokernel presentation along the kernel pair of `φ`. -/
def cokerDescentIso {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).obj (cokerAtlasModule f φ) ⟶
      (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).obj (cokerAtlasModule f φ) :=
  cokerSourceComparison f φ ≫ inv (cokerTargetComparison f φ)

/-- `cokerDescentIso` factors as `cokerSourceComparison ≫ inv cokerTargetComparison`. -/
theorem cokerDescentIso_spec {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    cokerDescentIso f φ =
      cokerSourceComparison f φ ≫ inv (cokerTargetComparison f φ) :=
  rfl

/-- The descent isomorphism of the cokernel presentation is an isomorphism. -/
instance cokerDescentIso_isIso {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    IsIso (cokerDescentIso f φ) :=
  sorry

/-- The groupoid action on the cokernel presentation of `Ω_{U/Y}`. -/
def cokerDescentAction {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).obj (cokerAtlasModule f φ) ⟶
      (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).obj (cokerAtlasModule f φ) :=
  inv (cokerDescentIso f φ)

/-- The action on the cokernel presentation satisfies the cocycle condition. -/
theorem cokerDescentAction_cocycle {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    GroupoidScheme.Cocycle (atlasGroupoid φ) (cokerAtlasModule f φ)
      (cokerDescentAction f φ) :=
  sorry

/-- The action on the cokernel presentation satisfies the unit condition. -/
theorem cokerDescentAction_unit {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] :
    GroupoidScheme.Unit (atlasGroupoid φ) (cokerAtlasModule f φ)
      (cokerDescentAction f φ) :=
  sorry

/-- The equivariant module given by the cokernel presentation of `Ω_{U/Y}`. -/
def cokerDescentSystem {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ] : (atlasGroupoid φ).QCoh :=
  GroupoidScheme.QCoh.of (cokerAtlasModule f φ) (cokerDescentAction f φ)
    (cokerDescentAction_cocycle f φ) (cokerDescentAction_unit f φ)

/-- The sheaf on `X` obtained by glueing the cokernel presentation of `Ω_{U/Y}`. -/
def cokerGlued {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ]
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ] : QCoh X :=
  (toGroupoid φ).inv.obj (cokerDescentSystem f φ)

/-- `cokerGlued` is the inverse image of `cokerDescentSystem` under the atlas descent
equivalence. -/
theorem cokerGlued_eq {X Y : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ Y) (φ : ofOver U ⟶ X) [Etale φ]
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ] :
    cokerGlued f φ = (toGroupoid φ).inv.obj (cokerDescentSystem f φ) :=
  rfl

/-- The module obtained by étale descent of scheme relative differentials is isomorphic
to the relative differential module on the algebraic space. -/
theorem glued_isIsomorphic_relativeDifferentials {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U Y : Over S} (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X)
    [Etale φ] [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ] :
    IsIsomorphic ((inclusion X).obj (glued f φ)) (relativeDifferentials f) :=
  sorry

/-- The module obtained by étale descent of the transitivity cokernel presentation is
isomorphic to the relative differential module on the algebraic space. -/
theorem cokerGlued_isIsomorphic_relativeDifferentials {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U : Over S} (f : X ⟶ Y) (φ : ofOver U ⟶ X)
    [Etale φ] [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ] :
    IsIsomorphic ((inclusion X).obj (cokerGlued f φ)) (relativeDifferentials f) :=
  sorry

/-- The module obtained by étale descent of relative differentials in an étale-vertical
presentation square is isomorphic to the relative differential module on the algebraic space. -/
theorem diagramGlued_isIsomorphic_relativeDifferentials {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U V : Over S} (f : X ⟶ Y) (ψ : U ⟶ V)
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) [Etale a] [Etale b]
    (sq : CommSq a (ofOverMap ψ) f b)
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a] :
    IsIsomorphic ((inclusion X).obj (diagramGlued f ψ a b sq)) (relativeDifferentials f) :=
  sorry

end Differentials
end Hom
end AlgebraicSpace
end AlgebraicGeometry
