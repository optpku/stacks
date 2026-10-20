module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.CompactGeneration
import StacksCheckRecall

/-!
# Lemma 61.15.1

The unbounded derived categories of abelian sheaves, `Λ`-modules, and modules
over a sheaf of rings, on both the small and the big pro-étale sites of a
scheme, are compactly generated.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits
universe u v w

/- Lemma 61.15.1 (1): `D(S_proétale)` is compactly generated. -/
@[stacks 0F4Q]
#check (AlgebraicGeometry.Scheme.ProEt.derivedAbelian_isCompactlyGenerated :
    ∀ (S : Scheme.{u})
      [HasSheafify (ProEt.topology S) AddCommGrpCat.{u + 1}]
      [Abelian (Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1})]
      [HasDerivedCategory (Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1})]
      [HasCoproducts (DerivedCategory (Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}))],
    IsCompactlyGenerated
      (DerivedCategory (Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1})))

/- Lemma 61.15.1 (2): `D(S_proétale, Λ)` is compactly generated. -/
@[stacks 0F4Q]
#check (AlgebraicGeometry.Scheme.ProEt.derivedModule_isCompactlyGenerated :
    ∀ (S : Scheme.{u}) (Λ : Type v) [Ring Λ]
      [HasWeakSheafify (ProEt.topology S) (ModuleCat.{v} Λ)]
      [Abelian (Sheaf (ProEt.topology S) (ModuleCat.{v} Λ))]
      [HasDerivedCategory (Sheaf (ProEt.topology S) (ModuleCat.{v} Λ))]
      [HasCoproducts (DerivedCategory (Sheaf (ProEt.topology S) (ModuleCat.{v} Λ)))],
    IsCompactlyGenerated
      (DerivedCategory (Sheaf (ProEt.topology S) (ModuleCat.{v} Λ))))

/- Lemma 61.15.1 (3): `D(S_proétale, A)` is compactly generated for any sheaf of
rings `A` on `S_proétale`. -/
@[stacks 0F4Q]
#check (AlgebraicGeometry.Scheme.ProEt.derivedSheafOfModules_isCompactlyGenerated :
    ∀ (S : Scheme.{u}) (A : Sheaf (ProEt.topology S) RingCat.{w})
      [UnivLE.{u + 1, w}]
      [Abelian (SheafOfModules.{w} A)]
      [HasDerivedCategory (SheafOfModules.{w} A)]
      [HasCoproducts (DerivedCategory (SheafOfModules.{w} A))],
    IsCompactlyGenerated (DerivedCategory (SheafOfModules.{w} A)))

/- Lemma 61.15.1 (4): `D((Sch/S)_proétale)` is compactly generated. -/
@[stacks 0F4Q]
#check (AlgebraicGeometry.Scheme.ProEt.bigDerivedAbelian_isCompactlyGenerated :
    ∀ (S : Scheme.{u})
      [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
      [Abelian (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
      [HasDerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
      [HasCoproducts
        (DerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1}))],
    IsCompactlyGenerated
      (DerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})))

/- Lemma 61.15.1 (5): `D((Sch/S)_proétale, Λ)` is compactly generated. -/
@[stacks 0F4Q]
#check (AlgebraicGeometry.Scheme.ProEt.bigDerivedModule_isCompactlyGenerated :
    ∀ (S : Scheme.{u}) (Λ : Type v) [Ring Λ]
      [HasWeakSheafify (proetaleTopology.over S) (ModuleCat.{v} Λ)]
      [Abelian (Sheaf (proetaleTopology.over S) (ModuleCat.{v} Λ))]
      [HasDerivedCategory (Sheaf (proetaleTopology.over S) (ModuleCat.{v} Λ))]
      [HasCoproducts
        (DerivedCategory (Sheaf (proetaleTopology.over S) (ModuleCat.{v} Λ)))],
    IsCompactlyGenerated
      (DerivedCategory (Sheaf (proetaleTopology.over S) (ModuleCat.{v} Λ))))

/- Lemma 61.15.1 (6): `D((Sch/S)_proétale, A)` is compactly generated for any
sheaf of rings `A` on `(Sch/S)_proétale`. -/
@[stacks 0F4Q]
#check (AlgebraicGeometry.Scheme.ProEt.bigDerivedSheafOfModules_isCompactlyGenerated :
    ∀ (S : Scheme.{u}) (A : Sheaf (proetaleTopology.over S) RingCat.{w})
      [UnivLE.{u + 1, w}]
      [Abelian (SheafOfModules.{w} A)]
      [HasDerivedCategory (SheafOfModules.{w} A)]
      [HasCoproducts (DerivedCategory (SheafOfModules.{w} A))],
    IsCompactlyGenerated (DerivedCategory (SheafOfModules.{w} A)))
