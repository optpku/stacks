module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.InfinitesimalAutomorphisms
import StacksCheckRecall

/-!
# Infinitesimal automorphisms of a predeformation category associated to a residue object

The group `Inf(ℱ_{𝒳, k, x₀})` is the kernel of
`Aut_{Spec(k[ε])}(x₀') → Aut_{Spec(k)}(x₀)`, where `x₀'` is a pullback of `x₀`
to `Spec(k[ε])`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver.Predeformation

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
variable (x0 : X.p.Fiber (Over.mk kToS))
variable (x0' : X.p.Fiber (specDualNumber openImmersion k))
variable (φ : Fiber.fiberInclusion.obj x0' ⟶ Fiber.fiberInclusion.obj x0)
variable [X.p.IsHomLift (specDualNumberToResidue openImmersion k kToS h_factor) φ]
variable [X.p.IsStronglyCartesian (specDualNumberToResidue openImmersion k kToS h_factor) φ]

/- 98.8.0.2: the group `Inf(ℱ_{𝒳, k, x₀})` of infinitesimal automorphisms is the kernel of
`Aut_{Spec(k[ε])}(x₀') → Aut_{Spec(k)}(x₀)`, where `x₀'` is a pullback of `x₀` to `Spec(k[ε])`. -/
@[stacks 07X0]
#check (AlgebraicGeometry.GroupoidsOver.Predeformation.infinitesimalAutomorphisms_eq_ker openImmersion kToS h_factor X x0 x0' φ :
    infinitesimalAutomorphisms openImmersion kToS h_factor X x0 x0' φ =
      (restrictAut openImmersion kToS h_factor X x0 x0' φ).ker)

end AlgebraicGeometry.GroupoidsOver.Predeformation
