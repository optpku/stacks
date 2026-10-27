/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChangeComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.Psi
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OfRepresentable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Correspondence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Invertible maps into relative Proj of algebraic spaces

A graded map from a pulled-back quasi-coherent algebra into the tensor powers of an
invertible module determines an open domain in the source, a morphism from that domain
into relative Proj, and a degreewise comparison of Serre twists with those powers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : X ⟶ Y)
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y)}
variable (deg : DegreePieces 𝒜) (L : X.Modules)

/-- A homomorphism of graded `𝒪_X`-algebras `f^* 𝒜 ⟶ ⊕_{n ≥ 0} L^{⊗ n}`, recorded by its
unlifted homogeneous components together with unit and multiplication laws. -/
structure GradedMapToPowers where
  /-- The degree-`n` component `f^* 𝒜_n ⟶ L^{⊗ n}`. -/
  hom :
    ∀ n : ℕ, (Modules.pullback f).obj (deg.obj n) ⟶ tensorPowerUnit L n
  /-- Degree zero sends the pulled-back unit of `𝒜` to the tensor-power unit. -/
  map_one :
    Modules.structureModulePullbackInv f ≫
        (Modules.pullback f).map (degreeZeroUnit deg) ≫ hom 0 =
      eqToHom (tensorPowerUnit_zero L).symm
  /-- Homogeneous multiplication is preserved. -/
  map_mul :
    ∀ i j : ℕ,
      pullbackTensorLax f (deg.obj i) (deg.obj j) ≫
          (Modules.pullback f).map (deg.mul i j) ≫ hom (i + j) =
        tensorHom (hom i) (hom j) ≫ (tensorPowerUnitAddIso L i j).hom

namespace GradedMapToPowers

/-- Assemble a graded map into tensor powers from its homogeneous components and algebra
laws. -/
def of
    (hom :
      ∀ n : ℕ, (Modules.pullback f).obj (deg.obj n) ⟶ tensorPowerUnit L n)
    (map_one :
      Modules.structureModulePullbackInv f ≫
          (Modules.pullback f).map (degreeZeroUnit deg) ≫ hom 0 =
        eqToHom (tensorPowerUnit_zero L).symm)
    (map_mul :
      ∀ i j : ℕ,
        pullbackTensorLax f (deg.obj i) (deg.obj j) ≫
            (Modules.pullback f).map (deg.mul i j) ≫ hom (i + j) =
          tensorHom (hom i) (hom j) ≫ (tensorPowerUnitAddIso L i j).hom) :
    GradedMapToPowers f deg L where
  hom := hom
  map_one := map_one
  map_mul := map_mul

/-- The unit and multiplication laws of a graded map into tensor powers hold
simultaneously. -/
theorem spec (ψ : GradedMapToPowers f deg L) :
    (Modules.structureModulePullbackInv f ≫
          (Modules.pullback f).map (degreeZeroUnit deg) ≫ ψ.hom 0 =
        eqToHom (tensorPowerUnit_zero L).symm) ∧
      ∀ i j : ℕ,
        pullbackTensorLax f (deg.obj i) (deg.obj j) ≫
            (Modules.pullback f).map (deg.mul i j) ≫ ψ.hom (i + j) =
          tensorHom (ψ.hom i) (ψ.hom j) ≫ (tensorPowerUnitAddIso L i j).hom :=
  ⟨ψ.map_one, ψ.map_mul⟩

/-- Two graded maps into tensor powers agree when every homogeneous component agrees. -/
theorem hom_ext (ψ ψ' : GradedMapToPowers f deg L)
    (h : ∀ n : ℕ, ψ.hom n = ψ'.hom n) : ψ = ψ' :=
  by
    cases ψ
    cases ψ'
    congr
    exact funext h

end GradedMapToPowers

/-- A unit-preserving multiplicative comparison from pulled-back nonnegative Serre twists
to the restricted tensor powers of a module on a fixed open subspace. -/
structure TwistComparison {F : ProjFunctor Y 𝒜} {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) (U : OpenSubspace X)
    (r : U.X ⟶ toAlgebraicSpace F hF) (L : X.Modules) where
  /-- The degree-`n` comparison
  `r^* 𝒪(n) ⟶ L^{⊗ n}|_{U(ψ)}`. -/
  hom :
    ∀ n : ℕ,
      (Modules.pullback r).obj (CanonicalTwists.obj F hF (Int.ofNat n)) ⟶
        (Modules.pullback U.ι).obj (tensorPowerUnit L n)
  /-- Degree zero of `θ` sends the pulled-back twist unit to the tensor-power unit. -/
  map_one :
    (Modules.pullback r).map (CanonicalTwists.unit F hF) ≫ hom 0 =
      (pullbackMonoidalUnitIso r).hom ≫
        Modules.structureModulePullbackInv U.ι ≫
          (Modules.pullback U.ι).map (eqToHom (tensorPowerUnit_zero L).symm)
  /-- Homogeneous multiplication is preserved by `θ`. -/
  map_mul :
    ∀ i j : ℕ,
      pullbackTensorLax r
            (CanonicalTwists.obj F hF (Int.ofNat i))
            (CanonicalTwists.obj F hF (Int.ofNat j)) ≫
          (Modules.pullback r).map
              (CanonicalTwists.mul F hF (Int.ofNat i) (Int.ofNat j)) ≫
            eqToHom
                (congrArg
                  (fun k : ℤ ↦
                    (Modules.pullback r).obj (CanonicalTwists.obj F hF k))
                  (Int.natCast_add i j).symm) ≫
              hom (i + j) =
        tensorHom (hom i) (hom j) ≫
          pullbackTensorLax U.ι
              (tensorPowerUnit L i) (tensorPowerUnit L j) ≫
            (Modules.pullback U.ι).map (tensorPowerUnitAddIso L i j).hom


namespace TwistComparison

variable {F : ProjFunctor Y 𝒜} {deg : DegreePieces 𝒜}
variable (hF : F.IsAssociatedToQuadruples deg) (U : OpenSubspace X)
variable (r : U.X ⟶ toAlgebraicSpace F hF) (L : X.Modules)

/-- Assemble a comparison from its homogeneous maps and algebra laws. -/
def of
    (hom :
      ∀ n : ℕ,
        (Modules.pullback r).obj (CanonicalTwists.obj F hF (Int.ofNat n)) ⟶
          (Modules.pullback U.ι).obj (tensorPowerUnit L n))
    (map_one :
      (Modules.pullback r).map (CanonicalTwists.unit F hF) ≫ hom 0 =
        (pullbackMonoidalUnitIso r).hom ≫
          Modules.structureModulePullbackInv U.ι ≫
            (Modules.pullback U.ι).map (eqToHom (tensorPowerUnit_zero L).symm))
    (map_mul :
      ∀ i j : ℕ,
        pullbackTensorLax r
              (CanonicalTwists.obj F hF (Int.ofNat i))
              (CanonicalTwists.obj F hF (Int.ofNat j)) ≫
            (Modules.pullback r).map
                (CanonicalTwists.mul F hF (Int.ofNat i) (Int.ofNat j)) ≫
              eqToHom
                  (congrArg
                    (fun k : ℤ ↦
                      (Modules.pullback r).obj (CanonicalTwists.obj F hF k))
                    (Int.natCast_add i j).symm) ≫
                hom (i + j) =
          tensorHom (hom i) (hom j) ≫
            pullbackTensorLax U.ι
                (tensorPowerUnit L i) (tensorPowerUnit L j) ≫
              (Modules.pullback U.ι).map (tensorPowerUnitAddIso L i j).hom) :
    TwistComparison hF U r L where
  hom := hom
  map_one := map_one
  map_mul := map_mul

/-- The unit and multiplication laws of `c.hom` hold simultaneously. -/
theorem spec (c : TwistComparison hF U r L) :
    ((Modules.pullback r).map (CanonicalTwists.unit F hF) ≫ c.hom 0 =
        (pullbackMonoidalUnitIso r).hom ≫
          Modules.structureModulePullbackInv U.ι ≫
            (Modules.pullback U.ι).map
              (eqToHom (tensorPowerUnit_zero L).symm)) ∧
      ∀ i j : ℕ,
        pullbackTensorLax r
              (CanonicalTwists.obj F hF (Int.ofNat i))
              (CanonicalTwists.obj F hF (Int.ofNat j)) ≫
            (Modules.pullback r).map
                (CanonicalTwists.mul F hF (Int.ofNat i) (Int.ofNat j)) ≫
              eqToHom
                  (congrArg
                    (fun k : ℤ ↦
                      (Modules.pullback r).obj (CanonicalTwists.obj F hF k))
                    (Int.natCast_add i j).symm) ≫
                c.hom (i + j) =
          tensorHom (c.hom i) (c.hom j) ≫
            pullbackTensorLax U.ι
                (tensorPowerUnit L i) (tensorPowerUnit L j) ≫
              (Modules.pullback U.ι).map
                (tensorPowerUnitAddIso L i j).hom :=
  ⟨c.map_one, c.map_mul⟩


/-- Two twist comparisons agree when all homogeneous components agree. -/
theorem hom_ext (c c' : TwistComparison hF U r L)
    (h : ∀ n, c.hom n = c'.hom n) : c = c' := by
  cases c
  cases c'
  congr
  exact funext h

end TwistComparison

variable {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : X ⟶ Y)
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y)}
variable (deg : DegreePieces 𝒜) {F : ProjFunctor Y 𝒜}
variable (hF : F.IsAssociatedToQuadruples deg) (L : X.Modules)
variable [isInvertibleObject L] (ψ : GradedMapToPowers f deg L)

/-- The restriction of `ψ` to a test morphism `w : T ⟶ X`, in degree `d`. -/
def restrictedDegreeMap {T : Over S} (w : ofOver T ⟶ X) (d : ℕ) :
    (Modules.pullback (w ≫ f)).obj (deg.obj d) ⟶
      tensorPowerUnit ((Modules.pullback w).obj L) d :=
  (Modules.pullbackCompIso w f).inv.app (deg.obj d) ≫
    (Modules.pullback w).map (ψ.hom d) ≫ pullbackTensorPowerHom w L d

/-- `restrictedDegreeMap` is composite-pullback comparison, then `ψ`, then the
tensor-power comparison. -/
theorem restrictedDegreeMap_eq {T : Over S} (w : ofOver T ⟶ X) (d : ℕ) :
    restrictedDegreeMap f deg L ψ w d =
      (Modules.pullbackCompIso w f).inv.app (deg.obj d) ≫
        (Modules.pullback w).map (ψ.hom d) ≫ pullbackTensorPowerHom w L d :=
  rfl

/-- Homogeneous components of the Veronese restriction of `ψ` along `w`, rebracketed as
maps into tensor powers of `L^{⊗ d}|_T`. -/
def restrictedPsi {T : Over S} (w : ofOver T ⟶ X) (d n : ℕ) :
    (Modules.pullback (w ≫ f)).obj (deg.obj (n * d)) ⟶
      tensorPowerUnit (tensorPowerUnit ((Modules.pullback w).obj L) d) n :=
  (Modules.pullbackCompIso w f).inv.app (deg.obj (n * d)) ≫
    (Modules.pullback w).map (ψ.hom (n * d)) ≫
      pullbackTensorPowerHom w L (n * d) ≫
        (tensorPowerUnitMulIso ((Modules.pullback w).obj L) d n).hom

/-- `restrictedPsi` is the degree-`(n * d)` component of `ψ`, rebracketed as a tensor power
of `L^{⊗ d}`. -/
theorem restrictedPsi_eq {T : Over S} (w : ofOver T ⟶ X) (d n : ℕ) :
    restrictedPsi f deg L ψ w d n =
      (Modules.pullbackCompIso w f).inv.app (deg.obj (n * d)) ≫
        (Modules.pullback w).map (ψ.hom (n * d)) ≫
          pullbackTensorPowerHom w L (n * d) ≫
            (tensorPowerUnitMulIso ((Modules.pullback w).obj L) d n).hom :=
  rfl

/-- The restricted Veronese components preserve the algebra laws, have invertible
 target, and are epimorphic in degree one. -/
theorem restrictedQuadruple_laws {T : Over S} (w : ofOver T ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    isInvertibleObject (tensorPowerUnit ((Modules.pullback w).obj L) d) ∧
    (Modules.structureModulePullbackInv (w ≫ f) ≫
      (Modules.pullback (w ≫ f)).map (degreeZeroUnit deg) ≫
      eqToHom (congrArg (fun k : ℕ ↦ (Modules.pullback (w ≫ f)).obj (deg.obj k))
        (Nat.zero_mul d).symm) ≫ restrictedPsi f deg L ψ w d 0 =
      eqToHom (tensorPowerUnit_zero (tensorPowerUnit ((Modules.pullback w).obj L) d)).symm) ∧
    (∀ i j : ℕ,
      pullbackTensorLax (w ≫ f) (deg.obj (i * d)) (deg.obj (j * d)) ≫
        (Modules.pullback (w ≫ f)).map (deg.mul (i * d) (j * d)) ≫
        eqToHom (congrArg (fun k : ℕ ↦ (Modules.pullback (w ≫ f)).obj (deg.obj k))
          (Nat.add_mul i j d).symm) ≫ restrictedPsi f deg L ψ w d (i + j) =
      tensorHom (restrictedPsi f deg L ψ w d i) (restrictedPsi f deg L ψ w d j) ≫
        (tensorPowerUnitAddIso (tensorPowerUnit ((Modules.pullback w).obj L) d) i j).hom) ∧
    Epi (restrictedPsi f deg L ψ w d 1) := sorry

/-- The relative projective quadruple `(d, T ⟶ Y, L^{⊗ d}|_T, ψ^{(d)}|_T)` on a test where
the degree-`d` map is an epimorphism. -/
def restrictedQuadruple {T : Over S} (w : ofOver T ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    Quadruple 𝒜 deg T :=
  Quadruple.of d hd (w ≫ f)
    (tensorPowerUnit ((Modules.pullback w).obj L) d) (restrictedQuadruple_laws f deg L ψ w d hd hEpi).1
    (restrictedPsi f deg L ψ w d)
    (restrictedQuadruple_laws f deg L ψ w d hd hEpi).2.1
    (restrictedQuadruple_laws f deg L ψ w d hd hEpi).2.2.1
    (restrictedPsi f deg L ψ w d 1) rfl
    (restrictedQuadruple_laws f deg L ψ w d hd hEpi).2.2.2


/-- The structure morphism of `restrictedQuadruple` is `w ≫ f`. -/
theorem restrictedQuadruple_morphism {T : Over S} (w : ofOver T ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    (restrictedQuadruple f deg L ψ w d hd hEpi).morphism = w ≫ f :=
  rfl

/-- The line bundle of `restrictedQuadruple` is `L^{⊗ d}|_T`. -/
theorem restrictedQuadruple_lineBundle {T : Over S} (w : ofOver T ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    (restrictedQuadruple f deg L ψ w d hd hEpi).lineBundle =
      tensorPowerUnit ((Modules.pullback w).obj L) d :=
  rfl

/-- A quasi-compact test morphism to `X` lies in `U(ψ)` when some positive-degree component
of `ψ` is an epimorphism. -/
def memDomainQc {T : Over S} [CompactSpace T.left] (w : ofOver T ⟶ X) : Prop :=
  ∃ d : ℕ, 1 ≤ d ∧ Epi (restrictedDegreeMap f deg L ψ w d)

/-- A general test morphism to `X` lies in `U(ψ)` when every quasi-compact open restriction
does. -/
def memDomain {T : Over S} (w : ofOver T ⟶ X) : Prop :=
  ∀ (V : T.left.Opens) [CompactSpace V.toScheme],
    memDomainQc f deg L ψ (ofOverMap (openOverι T V) ≫ w)

/-- On a quasi-compact test, membership in `U(ψ)` is existence of a positive-degree
epimorphism. -/
theorem memDomain_iff_exists_epi {T : Over S} [CompactSpace T.left]
    (w : ofOver T ⟶ X) :
    memDomain f deg L ψ w ↔
      ∃ d : ℕ, 1 ≤ d ∧ Epi (restrictedDegreeMap f deg L ψ w d) :=
  sorry

/-- A globally epimorphic positive-degree restriction lies in `U(ψ)`. -/
theorem memDomain_of_epi {T : Over S} (w : ofOver T ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    memDomain f deg L ψ w :=
  sorry

/-- Membership in the surjectivity domain is preserved by precomposition. -/
theorem memDomain_precomp {T T' : Over S} (g : T' ⟶ T)
    (t : X.functorOfPoints.obj (op T))
    (ht : memDomain f deg L ψ (pointHom t)) :
    memDomain f deg L ψ (pointHom (X.functorOfPoints.map g.op t)) := sorry

/-- The fppf subfunctor of `X` classified by `memDomain`. -/
def domainSubfunctor : Subfunctor X.functorOfPoints where
  obj T := {t | memDomain f deg L ψ (pointHom t)}
  map g t ht := memDomain_precomp f deg L ψ g.unop t ht

/-- The inclusion of `domainSubfunctor` is relatively representable. -/
theorem domain_relativelyRepresentable :
    yoneda.relativelyRepresentable (domainSubfunctor f deg L ψ).ι :=
  sorry

/-- The algebraic space underlying `U(ψ)`, obtained from the relatively representable
subfunctor of surjective-degree tests. -/
def domainSpace : AlgebraicSpace S :=
  ofRelativelyRepresentable (domainSubfunctor f deg L ψ).ι
    (domain_relativelyRepresentable f deg L ψ)

/-- The inclusion of the positive-degree surjectivity subfunctor is open. -/
theorem domain_openImmersion :
    IsOpenImmersion (ofRelativelyRepresentable_hom (domainSubfunctor f deg L ψ).ι
      (domain_relativelyRepresentable f deg L ψ)) := sorry

/-- The open subspace `U(ψ) ⊂ X`. -/
def domain : OpenSubspace X where
  X := domainSpace f deg L ψ
  ι := ofRelativelyRepresentable_hom (domainSubfunctor f deg L ψ).ι
      (domain_relativelyRepresentable f deg L ψ)
  isOpenImmersion := domain_openImmersion f deg L ψ

/-- The inclusion of `domain` is the subfunctor inclusion. -/
theorem domain_ι_eq :
    (domain f deg L ψ).ι =
      ofRelativelyRepresentable_hom (domainSubfunctor f deg L ψ).ι
        (domain_relativelyRepresentable f deg L ψ) :=
  rfl

/-- The functor of points of `domain` is the subfunctor of surjective-degree tests. -/
theorem domain_functorOfPoints :
    (domain f deg L ψ).X.functorOfPoints =
      (domainSubfunctor f deg L ψ).toFunctor :=
  rfl

/-- A chosen positive degree witnessing that a quasi-compact test lies in `U(ψ)`. -/
private def chosenDegree {T : Over S} [CompactSpace T.left] {w : ofOver T ⟶ X}
    (hw : memDomainQc f deg L ψ w) : ℕ :=
  @Nat.find _ (fun _ ↦ Classical.propDecidable _) hw

/-- The chosen degree is at least one. -/
private theorem chosenDegree_pos {T : Over S} [CompactSpace T.left] {w : ofOver T ⟶ X}
    (hw : memDomainQc f deg L ψ w) :
    1 ≤ chosenDegree f deg L ψ hw :=
  (@Nat.find_spec _ (fun _ ↦ Classical.propDecidable _) hw).1

/-- The restricted degree map in the chosen degree is an epimorphism. -/
private theorem chosenDegree_epi {T : Over S} [CompactSpace T.left] {w : ofOver T ⟶ X}
    (hw : memDomainQc f deg L ψ w) :
    Epi (restrictedDegreeMap f deg L ψ w (chosenDegree f deg L ψ hw)) :=
  (@Nat.find_spec _ (fun _ ↦ Classical.propDecidable _) hw).2

/-- The classifying point of a quasi-compact `U(ψ)`-test, via the restricted quadruple. -/
@[no_expose] def canonicalPointQc (T : Over S) [CompactSpace T.left]
    (x : {t : X.functorOfPoints.obj (op T) // memDomainQc f deg L ψ (pointHom t)}) :
    F.toFunctor.obj (op T) :=
  hF.pointOf T
    (restrictedQuadruple f deg L ψ (pointHom x.1)
      (chosenDegree f deg L ψ x.2)
      (chosenDegree_pos f deg L ψ x.2)
      (chosenDegree_epi f deg L ψ x.2))

/-- Quasi-compact restrictions of domain points lie in the surjectivity domain,
and their classifying points form a compatible family. -/
theorem canonicalPoint_laws (T : Over S)
    (x : {t : X.functorOfPoints.obj (op T) // memDomain f deg L ψ (pointHom t)}) :
    ∃ h : ∀ (V : T.left.Opens) [CompactSpace V.toScheme],
      memDomainQc f deg L ψ
        (pointHom (X.functorOfPoints.map (op (openOverι T V)) x.1)),
      ∀ (V W : T.left.Opens) [CompactSpace V.toScheme] [CompactSpace W.toScheme]
        (hle : V ≤ W),
        F.toFunctor.map (op (openOverιLE T hle))
          (canonicalPointQc f deg hF L ψ (openOver T W)
            ⟨X.functorOfPoints.map (op (openOverι T W)) x.1, h W⟩) =
          canonicalPointQc f deg hF L ψ (openOver T V)
            ⟨X.functorOfPoints.map (op (openOverι T V)) x.1, h V⟩ := sorry

/-- The classifying point of a general `U(ψ)`-test, glued from quasi-compact opens. -/
def canonicalPoint (T : Over S)
    (x : {t : X.functorOfPoints.obj (op T) // memDomain f deg L ψ (pointHom t)}) :
    F.toFunctor.obj (op T) :=
  (hF.qcLimit T).symm
    (ProjFunctor.QcCompatibleSystem.of
      (fun V _ ↦
        canonicalPointQc f deg hF L ψ (openOver T V)
          ⟨X.functorOfPoints.map (op (openOverι T V)) x.1, (canonicalPoint_laws f deg hF L ψ T x).choose V⟩)
      (canonicalPoint_laws f deg hF L ψ T x).choose_spec)


/-- `canonicalPointQc` is `pointOf` of the restricted quadruple. -/
theorem canonicalPointQc_eq (T : Over S) [CompactSpace T.left]
    (x : {t : X.functorOfPoints.obj (op T) // memDomainQc f deg L ψ (pointHom t)}) :
    canonicalPointQc f deg hF L ψ T x =
      hF.pointOf T
        (restrictedQuadruple f deg L ψ (pointHom x.1)
          (@Nat.find _ (fun _ ↦ Classical.propDecidable _) x.2)
          (@Nat.find_spec _ (fun _ ↦ Classical.propDecidable _) x.2).1
          (@Nat.find_spec _ (fun _ ↦ Classical.propDecidable _) x.2).2) :=
  by
    unfold canonicalPointQc chosenDegree
    rfl


/-- The classifying points of domain tests are natural under change of test scheme. -/
theorem canonicalMap_naturality :
    ∀ (T T' : (Over S)ᵒᵖ) (g : T ⟶ T'),
      (domainSubfunctor f deg L ψ).toFunctor.map g ≫
        TypeCat.ofHom (fun x ↦ canonicalPoint f deg hF L ψ T'.unop ⟨x.1, x.2⟩) =
      TypeCat.ofHom (fun x ↦ canonicalPoint f deg hF L ψ T.unop ⟨x.1, x.2⟩) ≫
        F.toFunctor.map g := sorry

/-- The morphism `r_{L,ψ} : U(ψ) ⟶ underline{Proj}_Y(𝒜)`, as a natural transformation of
functors of points. -/
def canonicalMap : (domain f deg L ψ).X ⟶ toAlgebraicSpace F hF where
  app T :=
    TypeCat.ofHom fun
      (x : (domainSubfunctor f deg L ψ).toFunctor.obj T) ↦
        canonicalPoint f deg hF L ψ T.unop ⟨x.1, x.2⟩
  naturality := canonicalMap_naturality f deg hF L ψ

/-- The canonical morphism `r_{L,ψ}` lies over `Y`. -/
theorem canonicalMap_over_base :
    canonicalMap f deg hF L ψ ≫ toAlgebraicSpace_hom F hF =
      (domain f deg L ψ).ι ≫ f :=
  sorry

/-- The adjoint of `ψ` in degree `d`, as a map `𝒜_d ⟶ f_* L^{⊗ d}`. -/
def psiPushforward (d : ℕ) :
    deg.obj d ⟶ (Modules.pushforward f).obj (tensorPowerUnit L d) :=
  ((Modules.pullbackPushforwardAdjunction f).homEquiv
      (deg.obj d) (tensorPowerUnit L d)) (ψ.hom d)

/-- Restriction of `f_* L^{⊗ d}` along `U(ψ) ⊂ X`. -/
def restrictPushforward (d : ℕ) :
    (Modules.pushforward f).obj (tensorPowerUnit L d) ⟶
      (Modules.pushforward ((domain f deg L ψ).ι ≫ f)).obj
        ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L d)) :=
  (Modules.pushforward f).map
      ((Modules.pullbackPushforwardAdjunction (domain f deg L ψ).ι).unit.app
        (tensorPowerUnit L d)) ≫
    (Modules.pushforwardComp (domain f deg L ψ).ι f).hom.app
      ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L d))

/-- Pushforward of `θ_d` along `π : underline{Proj}_Y(𝒜) ⟶ Y`, rewritten over `Y` via
`canonicalMap_over_base`. -/
def TwistComparison.pushforwardToBase
    (theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L)
    (d : ℕ) :
    (Modules.pushforward (toAlgebraicSpace_hom F hF)).obj
        (CanonicalTwists.obj F hF (Int.ofNat d)) ⟶
      (Modules.pushforward ((domain f deg L ψ).ι ≫ f)).obj
        ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L d)) :=
  (Modules.pushforward (toAlgebraicSpace_hom F hF)).map
      (((Modules.pullbackPushforwardAdjunction (canonicalMap f deg hF L ψ)).homEquiv
        (CanonicalTwists.obj F hF (Int.ofNat d))
        ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L d)))
      (theta.hom d)) ≫
    (Modules.pushforwardComp (canonicalMap f deg hF L ψ)
        (toAlgebraicSpace_hom F hF)).hom.app
      ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L d)) ≫
    eqToHom
      (congrArg
        (fun h ↦
          (Modules.pushforward h).obj
            ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L d)))
        (canonicalMap_over_base f deg hF L ψ))


/-- Every nonnegative homogeneous section square commutes for the supplied comparison. -/
def ThetaCompatible
    (theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L) : Prop :=
  ∀ d : ℕ,
    psiPushforward f deg L ψ d ≫ restrictPushforward f deg L ψ d =
      ((Modules.pullbackPushforwardAdjunction (toAlgebraicSpace_hom F hF)).homEquiv
        (deg.obj d) (CanonicalTwists.obj F hF (Int.ofNat d)))
        ((CanonicalTwists.psi F hF).hom d) ≫
      TwistComparison.pushforwardToBase f deg hF L ψ theta d

/-- A point of `|X|` lies in `|U(ψ)|` when it arises from a test in `memDomain`. -/
theorem domain_pointsSet_eq (x : Points X) :
    x ∈ (domain f deg L ψ).pointsSet ↔
      ∃ (T : Over S) (w : ofOver T ⟶ X),
        (∃ y : Points (ofOver T), Points.map w y = x) ∧ memDomain f deg L ψ w :=
  sorry


/-- Yoneda evaluation of a domain test belongs to the domain subfunctor. -/
theorem factorsThroughLift_mem {T : Over S} (w : ofOver T ⟶ X)
    (hw : memDomain f deg L ψ w) :
    (yonedaEquiv w) ∈ (domainSubfunctor f deg L ψ).obj (op T) := sorry

/-- A test morphism `w` that lies in `U(ψ)` factors through the open inclusion. -/
def factorsThroughLift {T : Over S} (w : ofOver T ⟶ X)
    (hw : memDomain f deg L ψ w) : ofOver T ⟶ (domain f deg L ψ).X :=
  yonedaEquiv.symm ⟨yonedaEquiv w, factorsThroughLift_mem f deg L ψ w hw⟩


/-- The lift along `U(ψ) ⊂ X` recovers `w`. -/
theorem factorsThroughLift_comp {T : Over S} (w : ofOver T ⟶ X)
    (hw : memDomain f deg L ψ w) :
    factorsThroughLift f deg L ψ w hw ≫ (domain f deg L ψ).ι = w :=
  sorry


/-- Epimorphicity of a restricted degree map is inherited by quasi-compact open
restrictions of the test. -/
theorem restrictedDegreeMap_epi_restrict {T : Over S} (w : ofOver T ⟶ X)
    (d : ℕ) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d))
    (V : T.left.Opens) [CompactSpace V.toScheme] :
    Epi (restrictedDegreeMap f deg L ψ (ofOverMap (openOverι T V) ≫ w) d) :=
  sorry


/-- Fixed-degree classifying points on quasi-compact opens form a compatible family. -/
theorem classifiedMapOfDegree_compatible {T : Over S} (w : ofOver T ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    ∀ (V W : T.left.Opens) [CompactSpace V.toScheme] [CompactSpace W.toScheme]
      (hle : V ≤ W),
      F.toFunctor.map (op (openOverιLE T hle))
        (hF.pointOf (openOver T W) (restrictedQuadruple f deg L ψ
          (ofOverMap (openOverι T W) ≫ w) d hd
          (restrictedDegreeMap_epi_restrict f deg L ψ w d hEpi W))) =
        hF.pointOf (openOver T V) (restrictedQuadruple f deg L ψ
          (ofOverMap (openOverι T V) ≫ w) d hd
          (restrictedDegreeMap_epi_restrict f deg L ψ w d hEpi V)) := sorry

/-- The morphism `T ⟶ underline{Proj}_Y(𝒜)` obtained from the relative projective quadruple construction by
gluing `hF.pointOf` of the restricted degree-`d` quadruple on quasi-compact opens
of `T`. -/
def classifiedMapOfDegree {T : Over S} (w : ofOver T ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    ofOver T ⟶ toAlgebraicSpace F hF :=
  yonedaEquiv.symm
    ((hF.qcLimit T).symm
      (ProjFunctor.QcCompatibleSystem.of
        (fun V _ ↦
          hF.pointOf (openOver T V)
            (restrictedQuadruple f deg L ψ
              (ofOverMap (openOverι T V) ≫ w) d hd
              (restrictedDegreeMap_epi_restrict f deg L ψ w d hEpi V)))
        (classifiedMapOfDegree_compatible f deg hF L ψ w d hd hEpi)))


/-- On a quasi-compact test, `classifiedMapOfDegree` is Yoneda inversion of
`pointOf` of the restricted quadruple in the given degree. -/
theorem classifiedMapOfDegree_eq {T : Over S} [CompactSpace T.left]
    (w : ofOver T ⟶ X) (d : ℕ) (hd : 1 ≤ d)
    (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    classifiedMapOfDegree f deg hF L ψ w d hd hEpi =
      yonedaEquiv.symm
        (hF.pointOf T (restrictedQuadruple f deg L ψ w d hd hEpi)) :=
  sorry


/-- For a general scheme test, the composite with `r_{L,ψ}` is the glueing of the
relative projective quadruple construction classifying maps on quasi-compact opens, using the same degree. -/
theorem classifiedMap_comp_of {W : Over S} (w : ofOver W ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    factorsThroughLift f deg L ψ w (memDomain_of_epi f deg L ψ w d hd hEpi) ≫
        canonicalMap f deg hF L ψ =
      classifiedMapOfDegree f deg hF L ψ w d hd hEpi :=
  sorry

/-- On a quasi-compact scheme test, the canonical morphism classifies the restricted
quadruple in any epimorphic positive degree. -/
theorem classifiedMap_comp {W : Over S} [CompactSpace W.left]
    (w : ofOver W ⟶ X) (d : ℕ) (hd : 1 ≤ d)
    (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    factorsThroughLift f deg L ψ w (memDomain_of_epi f deg L ψ w d hd hEpi) ≫
        canonicalMap f deg hF L ψ =
      yonedaEquiv.symm
        (hF.pointOf W (restrictedQuadruple f deg L ψ w d hd hEpi)) :=
  (classifiedMap_comp_of f deg hF L ψ w d hd hEpi).trans
    (classifiedMapOfDegree_eq f deg hF L ψ w d hd hEpi)


/-- There is a unique graded twist comparison on the surjectivity domain whose
homogeneous section squares commute with the input graded map. -/
theorem existsUnique_twistComparison :
    ∃! theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L,
      ThetaCompatible f deg hF L ψ theta := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
