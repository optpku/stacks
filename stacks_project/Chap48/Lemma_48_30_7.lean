module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Triangulated
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.ModuleDerived
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

universe v

/- Lemma 48.30.7: let `j : U ⟶ X` be an open immersion of Noetherian schemes and let `T`
be a positive inverse system of distinguished triangles `Kₙ ⟶ Lₙ ⟶ Mₙ ⟶ Kₙ[1]` in
`Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]`. If the pro-objects presented by `(Kₙ)` and
`(Mₙ)` are isomorphic to those of Deligne systems for `j`, then the pro-object presented by
`(Lₙ)` is also isomorphic to that of a Deligne system for `j`. -/
@[stacks 0G4Q] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.exists_proIso_middle_of_distinguished :
    ∀ {X U : Scheme.{v}} {j : U ⟶ X} [IsNoetherian X] [IsNoetherian U]
      [IsOpenImmersion j]
      (K L M : PNatInverseSystem
        Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
      (T : PNatInverseSystem (Pretriangulated.Triangle (DerivedCategory X.Modules)))
      (eK : T ⋙ Pretriangulated.Triangle.π₁ ≅
        K ⋙ ambient (SheafOfModules.isCoherent X.ringCatSheaf))
      (eL : T ⋙ Pretriangulated.Triangle.π₂ ≅
        L ⋙ ambient (SheafOfModules.isCoherent X.ringCatSheaf))
      (eM : T ⋙ Pretriangulated.Triangle.π₃ ≅
        M ⋙ ambient (SheafOfModules.isCoherent X.ringCatSheaf))
      (hT : ∀ n : ℕ+, T.stage n ∈
        Pretriangulated.distinguishedTriangles)
      (hK : ∃ S : DeligneSystem j,
        Nonempty (boundedProObject K ≅ S.proObject))
      (hM : ∃ S : DeligneSystem j,
        Nonempty (boundedProObject M ≅ S.proObject)),
      ∃ S : DeligneSystem j,
        Nonempty (boundedProObject L ≅ S.proObject))
