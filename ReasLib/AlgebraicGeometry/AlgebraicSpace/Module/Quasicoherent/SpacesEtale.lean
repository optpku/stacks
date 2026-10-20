module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces.AffineCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.EtaleLocal

/-!
# Quasi-coherent modules on the spaces-étale site

Quasi-coherence is preserved by étale restriction and is local for spaces-étale
covering families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Restriction along an étale morphism of algebraic spaces preserves quasi-coherence. -/
instance restrict_isQuasicoherent {S : Scheme.{u}} {Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) [Etale f] (F : Z.Modules) [F.IsQuasicoherent] :
    (restrict F f).IsQuasicoherent :=
  sorry

/-- A module is quasi-coherent if and only if its restrictions to every member of a
spaces-étale covering family are quasi-coherent. -/
theorem isQuasicoherent_iff_of_spacesEtaleCover {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : spacesEtaleSite X} {ι : Type u} [Small.{u} ι] {V : ι → spacesEtaleSite X}
    (f : ∀ i, V i ⟶ U) (hf : Presieve.ofArrows V f ∈ spacesEtalePrecoverage X U)
    (F : U.left.Modules) :
    F.IsQuasicoherent ↔ ∀ i, (restrict F (f i).left).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
