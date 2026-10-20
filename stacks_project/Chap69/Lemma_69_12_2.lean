module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Noetherian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
variable (F : X.Modules)

/- Lemma 69.12.2 (1): on a locally Noetherian algebraic space `X` over a scheme `S`, an
`𝒪_X`-module `F` is coherent iff it is a quasi-coherent finite type `𝒪_X`-module. -/
@[stacks 07UB]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType F :
  F.IsCoherent ↔ F.IsQuasicoherent ∧ F.IsFiniteType)

/- Lemma 69.12.2 (2): on a locally Noetherian algebraic space, coherence of an `𝒪_X`-module is
equivalent to finite presentation. -/
@[stacks 07UB]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isCoherent_iff_isFinitePresentation F :
  F.IsCoherent ↔ F.IsFinitePresentation)

/- Lemma 69.12.2 (3): `F` is coherent iff for every étale morphism `φ : ofOver U ⟶ X` from a
scheme, the pullback `(pullback φ).obj F` is coherent. -/
@[stacks 07UB]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isCoherent_iff_forall_etale F :
  F.IsCoherent ↔
    ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ], ((pullback φ).obj F).IsCoherent)

/- Lemma 69.12.2 (4): `F` is coherent iff there exists a surjective étale morphism
`φ : ofOver U ⟶ X` from a scheme such that `(pullback φ).obj F` is coherent. -/
@[stacks 07UB]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isCoherent_iff_exists_surjectiveEtale F :
  F.IsCoherent ↔
    ∃ (U : Over S) (φ : ofOver U ⟶ X),
      Etale φ ∧ Surjective φ ∧ ((pullback φ).obj F).IsCoherent)

/- Lemma 69.12.2 (5): in particular the structure module `𝒪_X` is coherent. -/
@[stacks 07UB]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.structureSheaf_isCoherent X :
  (SheafOfModules.unit (structureSheaf X) : X.Modules).IsCoherent)

/- The structure module of a locally Noetherian algebraic space is canonically coherent. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.instIsCoherentUnit X :
  (SheafOfModules.unit (structureSheaf X) : X.Modules).IsCoherent)

variable (L : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] in
/- Lemma 69.12.2 (6): in particular any invertible `𝒪_X`-module is coherent. -/
@[stacks 07UB]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isCoherent_of_isInvertible L : L.IsCoherent)

/- Invertible modules on a locally Noetherian algebraic space are canonically coherent. -/
variable (L : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] in
#check (AlgebraicGeometry.AlgebraicSpace.Modules.instIsCoherentOfIsInvertible L : L.IsCoherent)

variable [SheafOfModules.IsFiniteLocallyFree F] in
/- Lemma 69.12.2 (7): more generally any finite locally free `𝒪_X`-module is coherent. -/
@[stacks 07UB]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isCoherent_of_isFiniteLocallyFree F : F.IsCoherent)

/- Finite locally free modules on a locally Noetherian algebraic space are canonically
coherent. -/
variable [SheafOfModules.IsFiniteLocallyFree F] in
#check (AlgebraicGeometry.AlgebraicSpace.Modules.instIsCoherentOfIsFiniteLocallyFree F : F.IsCoherent)

end AlgebraicGeometry.AlgebraicSpace.Modules
