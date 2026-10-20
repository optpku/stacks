module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Kummer.Cohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 59.28.5 (1): for positive n invertible on S, étale roots-of-unity
cohomology is canonically the tensor-product group of equipped-pair classes. -/
@[stacks 040Q] #check (AlgebraicGeometry.Scheme.Modules.Kummer.h1EtaleEquivClasses :
  ∀ (S : Scheme.{u}) (n : ℕ), 0 < n →
    ∀ [HasSheafify (StandardTopology.etale.overTopology S) AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (StandardTopology.etale.overTopology S) AddCommGrpCat.{u + 1})],
      IsUnit (n : Γ(S, ⊤)) →
      (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
        (Scheme.AssociatedModule.bigCommStructureSheaf .etale S) n).H 1 ≃+
          Scheme.Modules.Kummer.Classes S n)

/- Lemma 59.28.5 (2): for positive n, fppf roots-of-unity cohomology is
canonically the tensor-product group of equipped-pair classes. -/
@[stacks 040Q] #check (AlgebraicGeometry.Scheme.Modules.Kummer.h1FppfEquivClasses :
  ∀ (S : Scheme.{u}) (n : ℕ), 0 < n →
    ∀ [HasSheafify (StandardTopology.fppf.overTopology S) AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (StandardTopology.fppf.overTopology S) AddCommGrpCat.{u + 1})],
      (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
        (Scheme.AssociatedModule.bigCommStructureSheaf .fppf S) n).H 1 ≃+
          Scheme.Modules.Kummer.Classes S n)

/- Lemma 59.28.5 (3): for positive n, syntomic roots-of-unity cohomology is
canonically the tensor-product group of equipped-pair classes. -/
@[stacks 040Q] #check (AlgebraicGeometry.Scheme.Modules.Kummer.h1SyntomicEquivClasses :
  ∀ (S : Scheme.{u}) (n : ℕ), 0 < n →
    ∀ [HasSheafify (StandardTopology.syntomic.overTopology S) AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (StandardTopology.syntomic.overTopology S) AddCommGrpCat.{u + 1})],
      (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
        (Scheme.AssociatedModule.bigCommStructureSheaf .syntomic S) n).H 1 ≃+
          Scheme.Modules.Kummer.Classes S n)

end
