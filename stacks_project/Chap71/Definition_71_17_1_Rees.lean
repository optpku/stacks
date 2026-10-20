module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Rees
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Graded
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap71.Definition_71_6_6_Sum
public import stacks_project.Chap71.Definition_71_7_1_AssociatedSheaf
public import stacks_project.Chap71.Lemma_71_11_11_Triple

/-!
# Rees algebras of quasi-coherent ideal sheaves on algebraic spaces

The Rees algebra of a quasi-coherent ideal sheaf `I` is the `ℤ`-graded
`𝒪_X`-algebra with degree `n` piece `I ^ n` for `n ≥ 0` and `0` for `n < 0`,
with homogeneous multiplication the image of the ideal-power action.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IdealSubobject.pow :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → IdealSubobject X → ℕ → IdealSubobject X)

#check (AlgebraicGeometry.AlgebraicSpace.reesAlgebraObj :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → IdealSubobject X → ℤ → X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.reesDegreeMul :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X) (n m : ℕ),
      (I.pow n).toModule ⊗ (I.pow m).toModule ⟶ (I.pow (n + m)).toModule)

#check (AlgebraicGeometry.AlgebraicSpace.reesAlgebra :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (I : IdealSubobject X) →
      [IsQuasiCoherent I] → GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X) ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.reesAlgebraDegreePieceIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
      [IsQuasiCoherent I] (n : ℕ),
      Modules.liftModule (I.pow n).toModule ≅ (reesAlgebra I).obj (Int.ofNat n))

#check (AlgebraicGeometry.AlgebraicSpace.reesDegreePieces :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (I : IdealSubobject X) →
      [IsQuasiCoherent I] → RelativeProj.DegreePieces (reesAlgebra I))

#check (AlgebraicGeometry.AlgebraicSpace.reesAlgebra_isQuasicoherent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I],
      GradedAlgebraSheaf.IsQuasicoherent.{u + 1, u} (reesAlgebra I))

#check (AlgebraicGeometry.AlgebraicSpace.reesAlgebra_isCommutative :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I],
      (reesAlgebra I).IsCommutative)
