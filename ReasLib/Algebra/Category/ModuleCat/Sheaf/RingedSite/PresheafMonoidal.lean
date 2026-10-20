/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal presentations of module presheaves on a ringed site

The module-presheaf category underlying a commutative ring sheaf has Mathlib's pointwise symmetric
monoidal structure.  This low-level presentation bridge is shared by explicit sheafification
constructions and by monoidal localization; it does not depend on a monoidal structure on module
sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (O : Sheaf J CommRingCat.{w})

namespace Presheaf

/-- The pointwise monoidal structure on module presheaves in the presentation underlying a
commutative ring sheaf. -/
@[stacks 03L6 "module-presheaf monoidal presentation"]
noncomputable instance monoidalCategory :
    MonoidalCategory (PresheafOfModules.{w} (ringSheaf J O).obj) :=
  PresheafOfModules.monoidalCategory (R := O.obj)

/-- The pointwise symmetric structure on module presheaves in the presentation underlying a
commutative ring sheaf. -/
@[stacks 03L6 "module-presheaf symmetric presentation"]
noncomputable instance symmetricCategory :
    SymmetricCategory (PresheafOfModules.{w} (ringSheaf J O).obj) :=
  PresheafOfModules.symmetricCategory (R := O.obj)

end Presheaf

namespace UnderlyingPresheaf

/-- The pointwise monoidal structure in Mathlib's opaque `sheafToPresheaf` presentation of the
underlying ring sheaf. -/
@[stacks 03L6 "underlying-presheaf monoidal presentation"]
noncomputable instance monoidalCategory :
    MonoidalCategory
      (PresheafOfModules.{w}
        ((sheafToPresheaf J RingCat.{w}).obj (ringSheaf J O))) :=
  Presheaf.monoidalCategory O

/-- The pointwise symmetry in Mathlib's opaque `sheafToPresheaf` presentation of the underlying
ring sheaf. -/
@[stacks 03L6 "underlying-presheaf symmetric presentation"]
noncomputable instance symmetricCategory :
    SymmetricCategory
      (PresheafOfModules.{w}
        ((sheafToPresheaf J RingCat.{w}).obj (ringSheaf J O))) :=
  Presheaf.symmetricCategory O

end UnderlyingPresheaf



end SheafOfModules.RingedSite.Tensor
