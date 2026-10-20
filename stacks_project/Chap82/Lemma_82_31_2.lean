module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.Dual
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ChernClass

universe u

/- Lemma 82.31.2: The degree-`i` Chern class of the dual of a finite locally free
module on a good algebraic space is `(-1)^i` times its degree-`i` Chern class. -/
@[stacks 0ESD] #check (AlgebraicGeometry.AlgebraicSpace.ChernClass.chernClass_dual :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ),
    chernClass δ f (Modules.dual E) i = ((-1 : ℤ) ^ i) • chernClass δ f E i)

#check (AlgebraicGeometry.AlgebraicSpace.ChernClass.chernClass_dual_cap :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
    (chernClass δ f (Modules.dual E) i).cap g k =
      ((-1 : ℤ) ^ i) • (chernClass δ f E i).cap g k)
