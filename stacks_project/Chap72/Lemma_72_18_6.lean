module

public import Mathlib.RingTheory.Length
public import Mathlib.Topology.Sober
public import stacks_project.Chap66.Lemma_66_29_4_Stalk
public import stacks_project.Chap72.Definition_72_18_3_Number
public import stacks_project.Chap72.Lemma_72_4_7_IntegralClosed

/-!
# Lemma 72.18.6

The intersection number of invertible modules with a closed subspace proper over
a field is the length-weighted sum of the intersection numbers of its
top-dimensional irreducible components.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace Intersection

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Lemma 72.18.6: in the situation of Definition 72.18.3, let `Z i ⊂ Z` be the
irreducible components of dimension `d`. Let
`m i = length_{𝒪_{X, x̄ i}}(𝒪_{Z, x̄ i})` where `x̄ i` is a geometric generic
point of `Z i`. Then
`(L 0 ⋯ L (d - 1) · Z) = ∑ m i (L 0 ⋯ L (d - 1) · Z i)`. -/
@[stacks 0EDI]
theorem number_eq_sum_irreducibleComponents {k : Type u} [Field k]
    {X Z : AlgebraicSpace (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper (toBase X)] [IsDecent X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    {ι : Type u} [Fintype ι]
    {Zi : ι → AlgebraicSpace (Spec (CommRingCat.of k))}
    (iZ : (a : ι) → Zi a ⟶ X)
    [∀ a, IsClosedImmersion (iZ a)] [∀ a, IsIntegral (Zi a)]
    [∀ a, IsLocallyNoetherian (Zi a)] [∀ a, Abelian (Zi a).Modules]
    [∀ a, HasInjectiveResolutions (Zi a).Modules]
    (xbar : ι → GeometricPoint X)
    (h_generic : ∀ a, IsGenericPoint (xbar a).image (Set.range (Points.map (iZ a))))
    (h_component : ∀ a,
      Maximal (fun s : Set (Points X) ↦
          _root_.IsIrreducible s ∧ s ⊆ Set.range (Points.map i))
        (Set.range (Points.map (iZ a))))
    (h_dim : ∀ a, dimension (Zi a) = d)
    (h_injective : Function.Injective fun a ↦ Set.range (Points.map (iZ a)))
    (h_exhaustive : ∀ T : IrreducibleCloseds (Points X),
      Maximal (fun s : Set (Points X) ↦
          _root_.IsIrreducible s ∧ s ⊆ Set.range (Points.map i))
          T.carrier →
        dimension (ClosedSubspace.ofIrreducibleClosed T).X = d →
          ∃ a, Set.range (Points.map (iZ a)) = T.carrier)
    (m : ι → ℕ)
    (h_length : ∀ a,
      Module.length (etaleLocalRing X (xbar a))
          (stalkModuleCat (xbar a)
            ((AlgebraicSpace.Modules.pushforward i).obj
              (SheafOfModules.unit (structureSheaf Z) : Z.Modules))) =
        m a) :
    number i hZdim L = ∑ a : ι, (m a : ℚ) * number (iZ a) (h_dim a) L := sorry

end Intersection
end AlgebraicGeometry.AlgebraicSpace.Modules
