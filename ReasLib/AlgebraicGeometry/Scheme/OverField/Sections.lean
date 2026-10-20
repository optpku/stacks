/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Global sections of scheme modules over a field

This leaf specializes the affine-base global-sections API to fields and gives
explicit algebra and module owners for an object of `Over (Spec k)`.
The general constructions live in `Scheme.GlobalSections` and
`Scheme.Module.Sections`.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k]
variable {X : Scheme.{u}}

/-- The global sections of a scheme module, as a `k`-module induced by a structural morphism
`f : X ⟶ Spec k`. This compatibility spelling exposes the unbundled module structure;
`globalSectionsMod f F` is the preferred object-level API. -/
@[stacks 01BH "global-sections module over a field"]
noncomputable abbrev globalSectionsModuleOverField
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) :
    Module k Γ(F, ⊤) :=
  globalSectionsModule f F

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The bundled global-sections functor of a scheme over `Spec k`. -/
@[stacks 01BH "global-sections functor over a field"]
noncomputable abbrev globalSectionsFunctor
    (X : Over (Spec (CommRingCat.of k))) : X.left.Modules ⥤ ModuleCat k :=
  Scheme.Hom.globalSectionsFunctor X.hom

/-- Global sections of a module sheaf on a scheme over `Spec k`, bundled as a `k`-module. -/
@[stacks 01BH "bundled global sections over a field"]
noncomputable abbrev globalSectionsMod
    (X : Over (Spec (CommRingCat.of k))) (F : X.left.Modules) : ModuleCat k :=
  (globalSectionsFunctor X).obj F

/-- The section ring on `U`, bundled as a `k`-algebra through the structure morphism of `X`. -/
@[stacks 01BH "bundled section algebra over a field"]
noncomputable abbrev sectionsAlg
    (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) : CommAlgCat k :=
  Scheme.Hom.sectionsAlgOverSpec X.hom U

/-- Sections of `F` on `U`, bundled as a `k`-module through the structure morphism of `X`. -/
@[stacks 01BH "bundled section module over a field"]
noncomputable abbrev sectionsMod
    (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens)
    (F : X.left.Modules) : ModuleCat k :=
  Scheme.Hom.sectionsModOverSpec X.hom U F

/-- The structure morphism of `X` gives the section ring on any open subset of `X` its
canonical `k`-algebra structure. This is an explicit construction rather than a global instance,
because the open subset is part of the intended scalar data. `sectionsAlg X U` is the preferred
object-level API. -/
@[stacks 01BH "section algebra over a field"]
noncomputable abbrev sectionsAlgebra
    (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    Algebra k Γ(X.left, U) :=
  Scheme.Hom.sectionsAlgebraOverSpec X.hom U

/-- The sections of a module sheaf on an open subset of a scheme over `Spec k`, viewed as a
`k`-module through the structure morphism of the scheme. `sectionsMod X U F` is the preferred
object-level API. -/
@[stacks 01BH "section module over a field"]
noncomputable abbrev sectionsModule
    (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) (F : X.left.Modules) :
    Module k Γ(F, U) :=
  Module.compHom Γ(F, U) (Scheme.Hom.sectionsMap X.hom U)

/-- The section-ring action and the section-module action induced by a scheme over `Spec k`
form a scalar tower. -/
@[stacks 01BH "section scalar tower over a field"]
theorem sectionsModule_isScalarTower
    (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) (F : X.left.Modules) :
    @IsScalarTower k Γ(X.left, U) Γ(F, U)
      (sectionsAlgebra X U).toSMul
      (inferInstance : SMul Γ(X.left, U) Γ(F, U))
      (sectionsModule X U F).toSMul := sorry

/-- The global sections of a module sheaf on a scheme over `Spec k`, with their canonical
`k`-module structure induced by the explicit global-sections map. -/
@[stacks 01BH "global-section module over a field"]
noncomputable abbrev globalSectionsModule
    (X : Over (Spec (CommRingCat.of k))) (F : X.left.Modules) :
    Module k Γ(F, ⊤) :=
  Module.compHom Γ(F, ⊤) (Scheme.Hom.globalSectionsMap X.hom)

end AlgebraicGeometry.SchemeOverField
