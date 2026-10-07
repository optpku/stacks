module

public import stacks_project.Chap66.Lemma_66_19_9_Exact
public import stacks_project.Chap66.Lemma_66_19_9_Representable
public import stacks_project.Chap66.Lemma_66_19_9_Stalk
import StacksCheckRecall

/-!
# Lemma 66.19.9

Inverse image along `f_small` is exact on abelian sheaves and on sheaves of sets, sends
sheafified representables to sheafified representables of fibre products, and identifies
stalks at geometric points with stalks at the image geometric point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

universe u

section ExactAb

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/- Lemma 66.19.9 (1): the functor `f_small⁻¹ : Ab(Y_étale) → Ab(X_étale)` is exact. -/
@[stacks 04K2] #check
  smallEtaleInverseImage_exact_addCommGrp f

end ExactAb

section ExactType

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/- Lemma 66.19.9 (2): the functor `f_small⁻¹ : Sh(Y_étale) → Sh(X_étale)` is exact, i.e. it
commutes with finite limits and finite colimits, see Categories, Definition 4.23.1. -/
@[stacks 04K2] #check
  smallEtaleInverseImage_exact_type f

end ExactType

section Representable

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (V : spacesEtaleSite Y)

/- Lemma 66.19.9 (3): for any étale morphism `V → Y` of algebraic spaces one has
`f_small⁻¹ h_V = h_{X ×_Y V}`, as sheaves on the étale sites of algebraic spaces, equivalently
on the small étale sites via Lemma 66.18.3. -/
@[stacks 04K2] #check
  smallEtaleInverseImage_representableIso f V

end Representable

section Stalk

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (xbar : GeometricPoint X)
variable [InitiallySmall
  ((spacesEtalePullback f ⋙ (toSpacesEtalePoint xbar).fiber).Elements)]
variable [((spacesEtalePullback f).sheafPushforwardContinuous (Type (u + 1))
    (spacesEtaleTopology Y) (spacesEtaleTopology X)).IsRightAdjoint]
variable (G : Sheaf (smallEtaleTopology Y) (Type (u + 1)))

/- Lemma 66.19.9 (4): there is a canonical identification `(f_small⁻¹ G)_x̄ ≅ G_ȳ` where
`ȳ = f ∘ x̄`. -/
@[stacks 04K2] #check
  smallEtaleInverseImage_stalkIso f xbar G

end Stalk
