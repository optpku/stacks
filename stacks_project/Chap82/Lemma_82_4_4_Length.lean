module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length

/-!
# Length of an 𝒪_X-module at a point, via an étale scheme chart

The restriction of an `𝒪_X`-module to a scheme étale over an algebraic space, and the
Zariski-stalk length of that restriction, give the source's finite-nonzero-length predicate
without choosing a numeric `lengthAt` invariant.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/- The restriction `F|_U` of an `𝒪_X`-module along an étale chart `φ : ofOver U ⟶ X` from a
scheme. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.etaleSchemeModule :
  ∀ {U : Over S} (φ : ofOver U ⟶ X) (F : X.Modules),
    U.left.Modules)

/- `etaleSchemeModule φ F` is the Zariski restriction of the étale pullback of `F`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.etaleSchemeModule_eq :
  ∀ {U : Over S} (φ : ofOver U ⟶ X) (F : X.Modules),
    etaleSchemeModule φ F = (restrictToScheme U).obj ((pullback φ).obj F))

/- The length of `F` at a point of an étale scheme chart, as the length of the Zariski stalk of
`etaleSchemeModule φ F`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.lengthOnEtaleChart :
  ∀ {U : Over S} (φ : ofOver U ⟶ X) (F : X.Modules) (u : U.left),
    ℕ∞)

/- `lengthOnEtaleChart` is the module length of the Zariski stalk of `etaleSchemeModule φ F`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.lengthOnEtaleChart_eq :
  ∀ {U : Over S} (φ : ofOver U ⟶ X) (F : X.Modules) (u : U.left),
    lengthOnEtaleChart φ F u =
      Module.length (U.left.presheaf.stalk u)
        (RingedSpace.stalkModuleCat (etaleSchemeModule φ F) u))

/- The length of `F` at `x ∈ |X|` is finite and nonzero: some étale scheme chart over `x` has
strictly positive finite Zariski-stalk length. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.hasFiniteNonzeroLengthAt :
  ∀ (F : X.Modules) (x : Points X),
    Prop)

/- `hasFiniteNonzeroLengthAt F x` unpacks as existence of an étale scheme chart over `x` with
finite nonzero length. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.hasFiniteNonzeroLengthAt_iff :
  ∀ (F : X.Modules) (x : Points X),
    hasFiniteNonzeroLengthAt F x ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ ∃ u : U.left,
          Points.mapOfOver φ u = x ∧
            0 < lengthOnEtaleChart φ F u ∧ lengthOnEtaleChart φ F u < ⊤)

/- A given étale scheme chart with finite nonzero length witnesses `hasFiniteNonzeroLengthAt`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.hasFiniteNonzeroLengthAt_of_lengthOnEtaleChart :
  ∀ {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : X.Modules) {u : U.left} {x : Points X} (hu : Points.mapOfOver φ u = x)
    (hpos : 0 < lengthOnEtaleChart φ F u) (htop : lengthOnEtaleChart φ F u < ⊤),
    hasFiniteNonzeroLengthAt F x)

end AlgebraicGeometry.AlgebraicSpace.Modules
