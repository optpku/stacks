module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Properties
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Properties
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Properties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.SymmetricPower
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open SheafOfModules
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

universe u

/- Lemma 17.21.5 (1) (01CK), tensor power: tensor powers preserve local generation by sections. -/
@[stacks 01CK "(1), tensor power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ)
    [IsLocallyGeneratedBySections F] ↦
  (TensorPower.isLocallyGeneratedBySections F n :
    IsLocallyGeneratedBySections (RingedSpace.TensorPower.sheaf F n))

/- Lemma 17.21.5 (1) (01CK), exterior power: exterior powers preserve local generation by sections. -/
@[stacks 01CK "(1), exterior power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ)
    [IsLocallyGeneratedBySections F] ↦
  (ExteriorPower.isLocallyGeneratedBySections F n :
    IsLocallyGeneratedBySections (Λ[n] F))

/- Lemma 17.21.5 (1) (01CK), symmetric power: symmetric powers preserve local generation by sections. -/
@[stacks 01CK "(1), symmetric power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ)
    [IsLocallyGeneratedBySections F] ↦
  (SymmetricPower.isLocallyGeneratedBySections F n :
    IsLocallyGeneratedBySections (Sym[n] F))

/- Lemma 17.21.5 (2) (01CK), tensor power: tensor powers preserve finite type. -/
@[stacks 01CK "(2), tensor power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [F.IsFiniteType] ↦
  (TensorPower.isFiniteType F n : (RingedSpace.TensorPower.sheaf F n).IsFiniteType)

/- Lemma 17.21.5 (2) (01CK), exterior power: exterior powers preserve finite type. -/
@[stacks 01CK "(2), exterior power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [F.IsFiniteType] ↦
  (ExteriorPower.isFiniteType F n : (Λ[n] F).IsFiniteType)

/- Lemma 17.21.5 (2) (01CK), symmetric power: symmetric powers preserve finite type. -/
@[stacks 01CK "(2), symmetric power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [F.IsFiniteType] ↦
  (SymmetricPower.isFiniteType F n : (Sym[n] F).IsFiniteType)

/- Lemma 17.21.5 (3) (01CK), tensor power: tensor powers preserve finite presentation. -/
@[stacks 01CK "(3), tensor power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [F.IsFinitePresentation] ↦
  (TensorPower.isFinitePresentation F n :
    (RingedSpace.TensorPower.sheaf F n).IsFinitePresentation)

/- Lemma 17.21.5 (3) (01CK), exterior power: exterior powers preserve finite presentation. -/
@[stacks 01CK "(3), exterior power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [F.IsFinitePresentation] ↦
  (ExteriorPower.isFinitePresentation F n : (Λ[n] F).IsFinitePresentation)

/- Lemma 17.21.5 (3) (01CK), symmetric power: symmetric powers preserve finite presentation. -/
@[stacks 01CK "(3), symmetric power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [F.IsFinitePresentation] ↦
  (SymmetricPower.isFinitePresentation F n : (Sym[n] F).IsFinitePresentation)

/- Lemma 17.21.5 (4) (01CK), tensor power: positive tensor powers of a coherent module sheaf are coherent. -/
@[stacks 01CK "(4), tensor power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [IsCoherent F] ↦
  (TensorPower.isCoherent_succ F n :
    IsCoherent (RingedSpace.TensorPower.sheaf F (n + 1)))

/- Lemma 17.21.5 (4) (01CK), exterior power: positive exterior powers of a coherent module sheaf are coherent. -/
@[stacks 01CK "(4), exterior power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [IsCoherent F] ↦
  (ExteriorPower.isCoherent_succ F n : IsCoherent (Λ[n + 1] F))

/- Lemma 17.21.5 (4) (01CK), symmetric power: positive symmetric powers of a coherent module sheaf are coherent. -/
@[stacks 01CK "(4), symmetric power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [IsCoherent F] ↦
  (SymmetricPower.isCoherent_succ F n : IsCoherent (Sym[n + 1] F))

/- Lemma 17.21.5 (5) (01CK), tensor power: tensor powers preserve quasi-coherence. -/
@[stacks 01CK "(5), tensor power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [F.IsQuasicoherent] ↦
  (TensorPower.isQuasicoherent F n :
    (RingedSpace.TensorPower.sheaf F n).IsQuasicoherent)

/- Lemma 17.21.5 (5) (01CK), exterior power: exterior powers preserve quasi-coherence. -/
@[stacks 01CK "(5), exterior power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [F.IsQuasicoherent] ↦
  (ExteriorPower.isQuasicoherent F n : (Λ[n] F).IsQuasicoherent)

/- Lemma 17.21.5 (5) (01CK), symmetric power: symmetric powers preserve quasi-coherence. -/
@[stacks 01CK "(5), symmetric power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [F.IsQuasicoherent] ↦
  (SymmetricPower.isQuasicoherent F n : (Sym[n] F).IsQuasicoherent)

/- Lemma 17.21.5 (6) (01CK), tensor power: tensor powers preserve local freeness. -/
@[stacks 01CK "(6), tensor power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [F.IsLocallyFree] ↦
  (TensorPower.isLocallyFree F n :
    (RingedSpace.TensorPower.sheaf F n).IsLocallyFree)

/- Lemma 17.21.5 (6) (01CK), exterior power: exterior powers preserve local freeness. -/
@[stacks 01CK "(6), exterior power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [F.IsLocallyFree] ↦
  (ExteriorPower.isLocallyFree F n : (Λ[n] F).IsLocallyFree)

/- Lemma 17.21.5 (6) (01CK), symmetric power: symmetric powers preserve local freeness. -/
@[stacks 01CK "(6), symmetric power"]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) [F.IsLocallyFree] ↦
  (SymmetricPower.isLocallyFree F n : (Sym[n] F).IsLocallyFree)

/- The generic fixed-rank refinement records the binomial rank of exterior powers. -/
#check @SheafOfModules.RingedSite.ExteriorPower.isFiniteLocallyFreeOfRank

/- Finite local freeness is registered as a single reusable property, so downstream arguments do
not need to rebuild the local-free and finite-type witnesses separately. -/
#check @SheafOfModules.RingedSite.ExteriorPower.isFiniteLocallyFree

/- The corresponding generic refinement for tensor powers records the multiplicative rank
formula `(rank F) ^ n`; this is the reusable API for later determinant and graded constructions. -/
#check @SheafOfModules.RingedSite.TensorPower.isFiniteLocallyFreeOfRank
#check @SheafOfModules.RingedSite.TensorPower.isFiniteLocallyFree
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] ↦
  (TensorPower.isFiniteLocallyFreeOfRank F n r :
    IsFiniteLocallyFreeOfRank (r ^ n) (RingedSpace.TensorPower.sheaf F n))
#check @SheafOfModules.RingedSite.SymmetricPower.isFiniteLocallyFreeOfRank
#check @SheafOfModules.RingedSite.SymmetricPower.isFiniteLocallyFree
#check fun {X : RingedSpace.{u}} (F : X.Modules) (n r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] ↦
  (SymmetricPower.isFiniteLocallyFreeOfRank F n r :
    IsFiniteLocallyFreeOfRank (Nat.multichoose r n) (Sym[n] F))
