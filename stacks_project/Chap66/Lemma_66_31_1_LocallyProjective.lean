module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import stacks_project.Chap66.«66_26_1_1_Restrict»

/-!
# Local projectivity along étale scheme morphisms

A quasi-coherent module on an algebraic space is checked for local projectivity after
restriction along étale morphisms from schemes, using affine-open sections in the small
étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of schemes over `S` that is étale as a morphism of schemes induces an étale
morphism of the associated algebraic spaces. -/
instance etale_ofOverMap {S : Scheme.{u}} {U V : Over S} (g : U ⟶ V)
    [AlgebraicGeometry.Etale g.left] : Etale (ofOverMap g) :=
  sorry

/-- The scheme over `S` obtained by viewing an affine open of `U` as an open subscheme of `U`. -/
def affineOpenOver {S : Scheme.{u}} {U : Over S} (V : U.left.affineOpens) : Over S :=
  Over.mk ((V : U.left.Opens).ι ≫ U.hom)

/-- The underlying scheme of `affineOpenOver V` is the affine open subscheme. -/
theorem affineOpenOver_left {S : Scheme.{u}} {U : Over S} (V : U.left.affineOpens) :
    (affineOpenOver V).left = (V : U.left.Opens) :=
  sorry

/-- The structure morphism of `affineOpenOver V` is the open immersion followed by `U.hom`. -/
theorem affineOpenOver_hom {S : Scheme.{u}} {U : Over S} (V : U.left.affineOpens) :
    (affineOpenOver V).hom = (V : U.left.Opens).ι ≫ U.hom :=
  sorry

/-- The open immersion of an affine open of `U`, as a morphism of algebraic spaces over `S`. -/
def affineOpenι {S : Scheme.{u}} {U : Over S} (V : U.left.affineOpens) :
    ofOver (affineOpenOver V) ⟶ ofOver U :=
  ofOverMap (Over.homMk (V : U.left.Opens).ι)

/-- `affineOpenι V` is `ofOverMap` of the over-morphism induced by the open immersion. -/
theorem affineOpenι_eq {S : Scheme.{u}} {U : Over S} (V : U.left.affineOpens) :
    affineOpenι V = ofOverMap (Over.homMk (V : U.left.Opens).ι) :=
  sorry

/-- The open immersion of an affine open is étale as a morphism of algebraic spaces. -/
instance etale_affineOpenι {S : Scheme.{u}} {U : Over S} (V : U.left.affineOpens) :
    Etale (affineOpenι V) :=
  sorry

/-- An affine open of a scheme `U` over `S`, as an object of the small étale site of `ofOver U`. -/
def affineOpenSite {S : Scheme.{u}} {U : Over S} (V : U.left.affineOpens) :
    smallEtaleSite (ofOver U) :=
  smallEtaleSite.mk (affineOpenι V)

/-- The underlying scheme over `S` of `affineOpenSite V` is `affineOpenOver V`. -/
theorem affineOpenSite_left {S : Scheme.{u}} {U : Over S} (V : U.left.affineOpens) :
    (affineOpenSite V).left = affineOpenOver V :=
  sorry

/-- The structure morphism of `affineOpenSite V` is `affineOpenι V`. -/
theorem affineOpenSite_hom {S : Scheme.{u}} {U : Over S} (V : U.left.affineOpens) :
    (affineOpenSite V).hom = affineOpenι V :=
  sorry

namespace Modules

/-- The restriction of `F` along an étale morphism from a scheme `U` is locally projective on
`U` when sections over every affine open of `U` are projective modules. -/
def isLocallyProjectiveOn {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    {U : Over S} (f : ofOver U ⟶ X) [Etale f] : Prop :=
  ∀ (V : U.left.affineOpens),
    Module.Projective ((structureSheaf (ofOver U)).obj.obj (op (affineOpenSite V)))
      ((restrict F f).val.obj (op (affineOpenSite V)))

/-- `isLocallyProjectiveOn F f` is affine-open sectionwise projectivity of `restrict F f`. -/
theorem isLocallyProjectiveOn_def {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    {U : Over S} (f : ofOver U ⟶ X) [Etale f] :
    isLocallyProjectiveOn F f ↔
      ∀ (V : U.left.affineOpens),
        Module.Projective ((structureSheaf (ofOver U)).obj.obj (op (affineOpenSite V)))
          ((restrict F f).val.obj (op (affineOpenSite V))) :=
  Iff.rfl

namespace isLocallyProjectiveOn

/-- Affine-open sectionwise projectivity of `restrict F f` witnesses `isLocallyProjectiveOn`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules} {U : Over S}
    {f : ofOver U ⟶ X} [Etale f]
    (h : ∀ (V : U.left.affineOpens),
      Module.Projective ((structureSheaf (ofOver U)).obj.obj (op (affineOpenSite V)))
        ((restrict F f).val.obj (op (affineOpenSite V)))) :
    isLocallyProjectiveOn F f :=
  h

/-- Sections of `restrict F f` over an affine open of `U` are projective. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules} {U : Over S}
    {f : ofOver U ⟶ X} [Etale f] (h : isLocallyProjectiveOn F f) (V : U.left.affineOpens) :
    Module.Projective ((structureSheaf (ofOver U)).obj.obj (op (affineOpenSite V)))
      ((restrict F f).val.obj (op (affineOpenSite V))) :=
  h V

end isLocallyProjectiveOn

/-- Local projectivity of `restrict F f`, with the étale hypothesis as an explicit parameter. -/
def isLocallyProjectiveOnWith {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    {U : Over S} (f : ofOver U ⟶ X) (hf : Etale f) : Prop :=
  @isLocallyProjectiveOn S X F U f hf

/-- `isLocallyProjectiveOnWith F f hf` agrees with `isLocallyProjectiveOn F f` when `f` is étale. -/
theorem isLocallyProjectiveOnWith_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    {U : Over S} (f : ofOver U ⟶ X) [Etale f] :
    isLocallyProjectiveOnWith F f ‹Etale f› ↔ isLocallyProjectiveOn F f :=
  Iff.rfl

/-- There exists a scheme `U` over `S` and a surjective étale morphism `U ⟶ X` such that the
restriction of `F` to `U` is locally projective on `U`. -/
def existsSurjectiveEtale {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) : Prop :=
  ∃ (U : Over S) (f : ofOver U ⟶ X) (hf : Etale f),
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
      isLocallyProjectiveOnWith F f hf

/-- `existsSurjectiveEtale F` is the existence of a surjective étale scheme atlas along which
`F` is locally projective. -/
theorem existsSurjectiveEtale_def {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    existsSurjectiveEtale F ↔
      ∃ (U : Over S) (f : ofOver U ⟶ X) (hf : Etale f),
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
          isLocallyProjectiveOnWith F f hf :=
  Iff.rfl

namespace existsSurjectiveEtale

/-- A surjective étale scheme atlas along which `F` is locally projective witnesses
`existsSurjectiveEtale F`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules} {U : Over S}
    (f : ofOver U ⟶ X) [Etale f]
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f)
    (hF : isLocallyProjectiveOn F f) : existsSurjectiveEtale F :=
  ⟨U, f, ‹Etale f›, h_surj, hF⟩

/-- An algebraic space satisfying `existsSurjectiveEtale F` admits a surjective étale scheme
atlas along which `F` is locally projective. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules}
    (h : existsSurjectiveEtale F) :
    ∃ (U : Over S) (f : ofOver U ⟶ X) (hf : Etale f),
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
        isLocallyProjectiveOnWith F f hf :=
  h

end existsSurjectiveEtale

/-- For every scheme `U` over `S` and every étale morphism `U ⟶ X`, the restriction of `F` to
`U` is locally projective on `U`. -/
def forallEtale {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) : Prop :=
  ∀ (U : Over S) (f : ofOver U ⟶ X) [Etale f], isLocallyProjectiveOn F f

/-- `forallEtale F` is the universal étale-scheme local projectivity condition. -/
theorem forallEtale_def {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    forallEtale F ↔ ∀ (U : Over S) (f : ofOver U ⟶ X) [Etale f], isLocallyProjectiveOn F f :=
  Iff.rfl

namespace forallEtale

/-- The universal étale-scheme local projectivity condition witnesses `forallEtale F`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules}
    (h : ∀ (U : Over S) (f : ofOver U ⟶ X) [Etale f], isLocallyProjectiveOn F f) :
    forallEtale F :=
  h

/-- If `forallEtale F`, then `F` is locally projective along every étale morphism from a
scheme. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules} (h : forallEtale F)
    {U : Over S} (f : ofOver U ⟶ X) [Etale f] : isLocallyProjectiveOn F f :=
  h U f

/-- An algebraic space satisfying `forallEtale F` has locally projective restriction along
every étale morphism from a scheme. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules} (h : forallEtale F) :
    ∀ (U : Over S) (f : ofOver U ⟶ X) [Etale f], isLocallyProjectiveOn F f :=
  h

end forallEtale

end Modules

end AlgebraicGeometry.AlgebraicSpace
