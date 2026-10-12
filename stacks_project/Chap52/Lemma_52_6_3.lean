/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocalizationAway.Ideal

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u v w z

namespace RingedSite
namespace Hom
namespace ModuleDerived

open LocalizationAway

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, z}]

/- Lemma 52.6.3: the sections whose localization-away homotopy limit vanishes are exactly
the sections of the ideal sheaf `ideal K`. -/
@[stacks 0998] #check (RingedSite.Hom.ModuleDerived.LocalizationAway.mem_ideal_iff :
    ∀ (K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O)
    (U : Cᵒᵖ) (f : O.obj.obj U),
    f ∈ IdealSheaf.sections (ideal K) U ↔ IsVanishingAt K U f)

end ModuleDerived
end Hom
end RingedSite
