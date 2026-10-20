module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.FiniteTypeGeneration
public import Mathlib.CategoryTheory.Monoidal.CommMon_
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The subalgebras of a commutative algebra object in scheme modules whose underlying
modules are quasi-coherent and of finite type. -/
def finiteTypeQuasiCoherentSubalgebras
    {X : Scheme.{u}} [MonoidalCategory X.Modules] [BraidedCategory X.Modules]
    (A : CommMon X.Modules) : Set (Subobject A) :=
  { B | ((B : CommMon X.Modules).X).IsQuasicoherent ∧
      ((B : CommMon X.Modules).X).IsFiniteType }

end AlgebraicGeometry.Scheme.Modules

/- Lemma 28.22.11: if `S` is quasi-compact and quasi-separated, every quasi-coherent
commutative `𝒪_S`-algebra is the directed colimit of its finite-type quasi-coherent
`𝒪_S`-subalgebras. -/
@[stacks 05JT] #check
  (AlgebraicGeometry.Scheme.QcAlgebraUnder.finiteTypeQuasiCoherentSubalgebras_isDirectedColimit :
    ∀ {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (A : S.QcAlgebraUnder),
      DirectedOn (· ≤ ·)
          (AlgebraicGeometry.Scheme.QcAlgebraUnder.finiteTypeQuasiCoherentSubalgebras A) ∧
        IsLUB
          (AlgebraicGeometry.Scheme.QcAlgebraUnder.finiteTypeQuasiCoherentSubalgebras A)
          (⊤ : Subobject A.obj))
