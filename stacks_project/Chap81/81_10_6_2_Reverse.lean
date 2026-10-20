module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalGlueing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing

universe u

/- The reverse module is the kernel of the canonical difference comparison. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing.reverse :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)), X.Modules)

/- The reverse kernel preserves quasi-coherence under the stated finiteness conditions. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing.reverse.instIsQuasicoherent :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f] [FinitePresentation i]
    (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i))
    [H.IsQuasicoherent] [G.IsQuasicoherent], (reverse f i H G φ).IsQuasicoherent)
