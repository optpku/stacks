/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.Proper

/-!
# Coherence of Higher Direct Images

This module records preservation of coherence by higher direct images along locally projective
and proper morphisms of schemes over locally Noetherian bases, and for coherent modules with
proper support along locally finite type morphisms.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- Every higher direct image of a coherent module along a locally projective morphism to a
locally Noetherian scheme is coherent. -/
@[stacks 02O4, instance]
theorem higherDirectImageModule_isCoherent_of_locallyProjective
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyProjective f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (i : ℕ) :
    (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ i).IsCoherent := sorry

/-- Every higher direct image of a coherent module along a proper morphism to a locally
Noetherian scheme is coherent. -/
@[stacks 02O5, instance]
theorem higherDirectImageModule_isCoherent_of_proper
    (f : X ⟶ S) [IsLocallyNoetherian S] [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (i : ℕ) :
    (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ i).IsCoherent := sorry

/-- Higher direct images of coherent modules along a morphism between schemes proper over a
field are coherent. -/
@[instance]
theorem higherDirectImageModule_isCoherent_of_proper_over_field
    {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (φ : Y ⟶ X)
    [hProperX : IsProper X.hom] [hProperY : IsProper Y.hom]
    (𝒢 : Y.left.Modules) [𝒢.IsCoherent] (i : ℕ) :
    (RingedSpace.Hom.higherDirectImageModule φ.left.toShHom 𝒢 i).IsCoherent := sorry

namespace HigherDirectImage

/-- Every higher direct image of a coherent module with proper support along a locally finite type
morphism to a locally Noetherian scheme is coherent. -/
@[stacks 08DS, instance]
theorem isCoherent_of_properSupport
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsCoherent] [Modules.HasProperSupportOver f ℱ] (p : ℕ) :
    (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ p).IsCoherent := sorry

end HigherDirectImage

end AlgebraicGeometry.Scheme
