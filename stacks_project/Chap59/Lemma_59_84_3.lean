module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Finiteness
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/- Lemma 59.84.3: finite generation of constructible module-sheaf étale cohomology
on a separated finite-type curve over an algebraically closed field is unchanged
by restriction to a dense open subscheme and extension by zero. -/
@[stacks 0GJE] #check
  (AlgebraicGeometry.Scheme.Etale.finiteCohomology_iff_extensionByZero :
    ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {k : Type v} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    {X' : Scheme.{v}} (j : X' ⟶ X.left) [IsOpenImmersion j]
    (h_dense : Dense (Set.range j.base)) (q : ℕ)
    [∀ Y : Scheme.{v}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [∀ (Y : Scheme.{v}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{max u (v + 1)} Λ)]
    [∀ (Y : Scheme.{v}) (f : Y ⟶ X.left)
      (P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{max u (v + 1)} Λ),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [∀ P : X'.Etaleᵒᵖ ⥤ ModuleCat.{max u (v + 1)} Λ,
      (etaleRestriction j).op.HasLeftKanExtension P]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasExt (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [X.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ))
    (hF : CategoryTheory.Sheaf.IsConstructibleEtale
      (fun {Y} f => ((smallEtalePullback f).sheafPullback
        (ModuleCat.{max u (v + 1)} Λ) X.left.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G => CategoryTheory.Sheaf.IsLocallyConstantWith
        (fun M : ModuleCat.{max u (v + 1)} Λ => Module.Finite Λ M) G) F),
    Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor (J := X.left.smallEtaleTopology) (A := Λ) q).obj F) ↔
      Module.Finite Λ
        ((siteModuleCohomologyModuleFunctor (J := X.left.smallEtaleTopology) (A := Λ) q).obj
          ((etaleExtensionByZero j (ModuleCat.{max u (v + 1)} Λ)).obj
            ((etaleRestrictionSheaf j (ModuleCat.{max u (v + 1)} Λ)).obj F))))

end AlgebraicGeometry.Scheme

end
