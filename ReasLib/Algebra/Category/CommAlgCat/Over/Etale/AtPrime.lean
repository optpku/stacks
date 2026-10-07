module

public import ReasLib.Algebra.Category.CommAlgCat.Over.Etale.Localization
public import ReasLib.Algebra.Category.CommAlgCat.Over.Etale.Neighborhood
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pointed etale geometry at a prime

This leaf specializes the general category of pointed etale algebras to the
canonical residue-field target `κ(p)`. It owns only the prime-indexed views:
the category, its source diagram, its prime-localized diagram, and the bridge
to `PrimeSpectrum.EtaleNeighborhood`. General filteredness is supplied by
`CommAlgCat.Over.Etale.instIsFiltered`, so no prime-specific wrapper is needed.

@stack 04GV
-/

open CategoryTheory

universe u

namespace CommAlgCat.Over.Etale.AtPrime

variable {R : Type u} [CommRing R]

/-- The spectrum point represented by a prime ideal. -/
@[stacks 04GV "prime point for the pointed etale category"]
def point (p : Ideal R) [p.IsPrime] : PrimeSpectrum R :=
  ⟨p, inferInstance⟩

/-- The category of etale `R`-algebras pointed at the residue field of `p`. -/
@[stacks 04GV "prime-indexed pointed etale category"]
abbrev category (p : Ideal R) [p.IsPrime] :=
  CommAlgCat.Over.Etale.category R p.ResidueField

/-- The source diagram of pointed etale `R`-algebras at `p`. -/
@[stacks 04GV "source diagram of prime-indexed pointed etale algebras"]
noncomputable abbrev sourceDiagram (p : Ideal R) [p.IsPrime] :
    category p ⥤ CommAlgCat R :=
  CommAlgCat.Over.Etale.diagram R p.ResidueField

/-- The diagram obtained by localizing every pointed etale algebra at its
selected prime over `p`. -/
@[stacks 04GV "localized diagram of prime-indexed pointed etale algebras"]
noncomputable abbrev localizedDiagram (p : Ideal R) [p.IsPrime] :
    category p ⥤ CommAlgCat (Localization.AtPrime p) :=
  CommAlgCat.Over.Etale.Localization.diagram
    (Ideal.ker_algebraMap_residueField (I := p))

/-- The geometric etale neighborhood represented by a pointed etale algebra
at the prime `p`. -/
@[stacks 04GV "prime-indexed pointed etale neighborhood"]
noncomputable def neighborhood (p : Ideal R) [p.IsPrime] (A : category p) :
    PrimeSpectrum.EtaleNeighborhood (point p) :=
  CommAlgCat.Over.Etale.toNeighborhood (point p) A

end CommAlgCat.Over.Etale.AtPrime
