/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Gerbe.Basic

/-!
# Gerbes and fiberwise isomorphism classes

For a projection already known to be a stack in groupoids, the two local gerbe conditions say
precisely that its presheaf of fiberwise isomorphism classes is locally terminal.  This
formulation does not expose the default cleavage used by the coverwise source definition.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]
variable {J : GrothendieckTopology C} {p : S ⥤ C}

namespace IsGerbe.FiberClasses

/-- Definition 8.11.1 (tag 06NZ): for a stack in groupoids, the gerbe condition is equivalent
to local surjectivity and local injectivity of the canonical map from fiberwise isomorphism
classes to the terminal presheaf. -/
@[stacks 06NZ "gerbe fiber-class criterion"]
theorem iff [IsStack.InGroupoids J p] :
    IsGerbe J p ↔
      Presheaf.IsLocallySurjective J
          (terminal.from (Functor.fiberIsoClassPresheaf p)) ∧
        Presheaf.IsLocallyInjective J
          (terminal.from (Functor.fiberIsoClassPresheaf p)) := sorry

/-- Local inhabitedness and local connectedness of fiberwise isomorphism classes construct the
gerbe condition for a projection already known to be a stack in groupoids. -/
@[stacks 06NZ "gerbe fiber-class constructor"]
theorem of
    [IsStack.InGroupoids J p]
    (h_surjective : Presheaf.IsLocallySurjective J
      (terminal.from (Functor.fiberIsoClassPresheaf p)))
    (h_injective : Presheaf.IsLocallyInjective J
      (terminal.from (Functor.fiberIsoClassPresheaf p))) :
    IsGerbe J p := sorry

end IsGerbe.FiberClasses

end CategoryTheory
