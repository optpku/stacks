/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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

/- Lemma 28.22.1 (1): for a quasi-compact open immersion `j : U ⟶ X`, every quasi-coherent
module on `U` extends to a quasi-coherent module on `X`. -/
@[stacks 01PE]
#check (AlgebraicGeometry.Scheme.Modules.exists_quasiCoherentExtension :
  ∀ (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (G : U.Modules) [G.IsQuasicoherent],
    ∃ H : X.Modules, H.IsQuasicoherent ∧ Nonempty (H.restrict j ≅ G))

/- Lemma 28.22.1 (2): a quasi-coherent subobject of the restriction of a quasi-coherent module
along a quasi-compact open immersion extends compatibly to a quasi-coherent subobject. -/
@[stacks 01PE]
#check (AlgebraicGeometry.Scheme.Modules.exists_quasiCoherentSubsheafExtension :
  ∀ (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) [F.IsQuasicoherent]
    (G : Subobject (F.restrict j)) [(G : U.Modules).IsQuasicoherent],
    ∃ H : Subobject F,
      (H : X.Modules).IsQuasicoherent ∧
        ∃ e : (H : X.Modules).restrict j ≅ (G : U.Modules),
          e.hom ≫ G.arrow = (restrictFunctor j).map H.arrow)

/- Lemma 28.22.1 (3): a morphism from a quasi-coherent module on `U` to the restriction of a
quasi-coherent module on `X` extends compatibly along a quasi-compact open immersion. -/
@[stacks 01PE]
#check (AlgebraicGeometry.Scheme.Modules.exists_quasiCoherentMorphismExtension :
  ∀ (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) [F.IsQuasicoherent]
    (G : U.Modules) [G.IsQuasicoherent] (φ : G ⟶ F.restrict j),
    ∃ H : X.Modules,
      H.IsQuasicoherent ∧
        ∃ ψ : H ⟶ F, ∃ e : H.restrict j ≅ G,
          e.hom ≫ φ = (restrictFunctor j).map ψ)

end AlgebraicGeometry.Scheme.Modules
