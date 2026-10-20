module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.OpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}}

/- Lemma 28.22.2: on a quasi-compact quasi-separated scheme, a finite-type quasi-coherent
subobject over a quasi-compact open subscheme extends compatibly to a finite-type
quasi-coherent subobject of the ambient quasi-coherent module. -/
@[stacks 01PF]
#check (AlgebraicGeometry.Scheme.Modules.exists_finiteTypeQuasiCoherentSubsheafExtension :
  ∀ {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) [F.IsQuasicoherent]
    (G : Subobject (F.restrict j))
    [(G : U.Modules).IsQuasicoherent] [(G : U.Modules).IsFiniteType],
    ∃ H : Subobject F,
      (H : X.Modules).IsQuasicoherent ∧ (H : X.Modules).IsFiniteType ∧
        ∃ e : (H : X.Modules).restrict j ≅ (G : U.Modules),
          e.hom ≫ G.arrow = (restrictFunctor j).map H.arrow)

end AlgebraicGeometry.Scheme.Modules
