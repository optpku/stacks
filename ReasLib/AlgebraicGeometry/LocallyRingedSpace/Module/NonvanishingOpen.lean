module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NonvanishingOpen
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Sections

/-!
# Pullback of nonvanishing opens on locally ringed spaces

Nonvanishing of a module section is preserved and reflected by the local maps on stalks induced by
a morphism of locally ringed spaces. The underlying locus statement does not require the module
to be invertible; invertibility is used only to package the locus as an open subset.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}}

namespace Hom

/-- Pullback of a compatible global module section along a morphism of locally ringed spaces. -/
@[stacks 0H78 "pullback of sections"]
noncomputable abbrev pullbackSections (f : Y ⟶ X) {L : X.Modules} (s : L.sections) :
    ((RingedSpace.Hom.pullback f.toShHom).obj L).sections :=
  RingedSpace.Hom.pullbackSections f.toShHom s

end Hom

namespace SectionNonvanishing

/-- The nonvanishing locus of a module section pulls back along every morphism of locally ringed
spaces. No invertibility hypothesis is needed at the level of underlying loci. -/
theorem preimage_locus (f : Y ⟶ X) (L : X.Modules) (s : L.sections) :
    f.base ⁻¹' RingedSpace.sectionNonvanishingLocus X.toRingedSpace L s =
      RingedSpace.sectionNonvanishingLocus Y.toRingedSpace
        ((RingedSpace.Hom.pullback f.toShHom).obj L) (Hom.pullbackSections f s) := sorry

/-- Remark 17.25.11 (0H78): the inverse image of the nonvanishing open of a section of an
invertible module sheaf is the nonvanishing open of its pulled-back section. -/
@[stacks 0H78]
theorem comap_open (f : Y ⟶ X) (L : X.Modules)
    [MonoidalCategory.isInvertibleObject L] (s : L.sections) :
    Opens.comap f.base.hom (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L s) =
      RingedSpace.sectionNonvanishingOpen Y.toRingedSpace
        ((RingedSpace.Hom.pullback f.toShHom).obj L) (Hom.pullbackSections f s) := sorry

end SectionNonvanishing

end AlgebraicGeometry.LocallyRingedSpace
