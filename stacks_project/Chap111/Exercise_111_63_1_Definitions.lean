module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)

/- Exercise 111.63.1 (Definitions) (1): a scheme. -/
@[stacks 0G13] #check Scheme

#check Scheme.forgetToLocallyRingedSpace

/- Exercise 111.63.1 (Definitions) (2): a morphism of schemes is a morphism of the
underlying locally ringed spaces. -/
@[stacks 0G13] #check Scheme.Hom

#check Scheme.Hom.toLRSHom
#check (inferInstance : Category Scheme.{u})

/- Exercise 111.63.1 (Definitions) (3): a quasi-coherent module on a scheme. -/
@[stacks 0G13] #check (F.IsQuasicoherent : Prop)

section
variable {k : Type u} [Field k] (V : SchemeOverField k)

/- Exercise 111.63.1 (Definitions) (4): a variety over a field `k`. -/
@[stacks 0G13] #check (Variety V : Prop)

#check (variety_iff V :
  Variety V ↔ IsIntegral V.left ∧ IsSeparated V.hom ∧ Scheme.Hom.FiniteType V.hom)

/- Exercise 111.63.1 (Definitions) (5): a curve over a field `k`. -/
@[stacks 0G13] #check (Curve V : Prop)

#check (curve_iff V : Curve V ↔ Variety V ∧ topologicalKrullDim V.left = 1)

end

/- Exercise 111.63.1 (Definitions) (6): a finite morphism of schemes. -/
@[stacks 0G13] #check (IsFinite f : Prop)

#check (isFinite_iff f :
  IsFinite f ↔
    IsAffineHom f ∧
      ∀ U : Y.Opens, IsAffineOpen U → (f.app U).hom.Finite)

section
open TopologicalSpace

variable {X : TopCat.{u}} (F : X.Sheaf AddCommGrpCat.{u})
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]

/- Exercise 111.63.1 (Definitions) (7): the cohomology of a sheaf of abelian groups `F`
over a topological space `X`. -/
@[stacks 0G13] #check fun n : ℕ ↦ F.H n

#check fun n : ℕ ↦ F.H' n (⊤ : Opens X)

end

/- Exercise 111.63.1 (Definitions) (8): a dualizing sheaf on a scheme `X` of dimension `d`
proper over a field `k`. The dimension `d` is `dimensionIndex f`. -/
@[stacks 0G13] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f], X.Modules)

#check AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dimensionIndex
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule_eq

/- Exercise 111.63.1 (Definitions) (9): a rational map from a variety `X` to a variety `Y`.
The canonical owner is scheme-level; the exam varieties are a comment-level specialization. -/
@[stacks 0G13] #check (X ⤏ Y)

#check AlgebraicGeometry.Scheme.PartialMap.toRationalMap
#check AlgebraicGeometry.Scheme.RationalMap.exists_rep
#check AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff
