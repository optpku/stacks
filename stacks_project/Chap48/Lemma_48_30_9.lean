module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

/- Lemma 48.30.9: let `j : U ⟶ X` be an open immersion of Noetherian schemes, let
`a ≤ b`, and let `K` be a positive inverse system in
`Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]` whose cohomology vanishes outside `[a, b]`.
Then the pro-object presented by `K` is isomorphic to that of a Deligne system if and only if,
for one fixed ideal `I` cutting out `X \ U` and every `p : ℤ`, there is a coherent module `F`
such that the degree-`p` cohomology system of `K` and the positive system `(I ^ n F)` present
isomorphic pro-objects. The same fixed ideal `I` is used in every degree. -/
@[stacks 0G4S] #check (@AlgebraicGeometry.Scheme.ModuleDerived.exists_proIso_deligne_iff_cohomology :
  ∀ {X U : Scheme.{v}} {j : U ⟶ X} [IsNoetherian X] [IsNoetherian U]
    [IsOpenImmersion j]
    (a b : ℤ) (hab : a ≤ b)
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange)
    (K : PNatInverseSystem
      (@DerivedCategory.Bounded.CohomologyIn X.Modules _ _
        (AlgebraicGeometry.Scheme.Modules.schemeModulesHasDerivedCategory X)
        (SheafOfModules.isCoherent X.ringCatSheaf)))
    (hK : ∀ n : ℕ+, ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((AlgebraicGeometry.Scheme.ModuleDerived.BoundedSystem.cohomology K i).stage n)),
    (∃ S : AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem j,
        Nonempty
          (AlgebraicGeometry.Scheme.ModuleDerived.boundedProObject K ≅ S.proObject)) ↔
      ∀ p : ℤ,
        ∃ F : (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory,
          Nonempty
            ((@Pro.lim X.Modules _ (OrderDual ℕ+) _ _ _ _).obj
                (AlgebraicGeometry.Scheme.ModuleDerived.BoundedSystem.cohomology K p) ≅
              (@Pro.lim X.Modules _ (OrderDual ℕ+) _ _ _ _).obj
                (AlgebraicGeometry.Scheme.Modules.IdealPowerProduct.positiveSystem I F.obj)))
