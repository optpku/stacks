/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ToTerminal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

section Affine

variable (X : Scheme.{u}) [IsAffine X]

/- Remark 26.21.18 (1): affine schemes have the absolute compactness and separation properties
used in the remark. -/
@[stacks 0816] #check (inferInstance : CompactSpace X)
@[stacks 0816] #check (inferInstance : QuasiSeparatedSpace X)
@[stacks 0816] #check (inferInstance : X.IsSeparated)

end Affine

/- Remark 26.21.18: quasi-compact, quasi-separated, and separated absolute properties are the
terminal-object forms of the corresponding morphism properties. -/
@[stacks 0816] #check quasiCompact_toTerminal_iff
@[stacks 0816] #check quasiSeparated_toTerminal_iff
@[stacks 0816] #check isSeparated_toTerminal_iff
#check MorphismProperty.toTerminal_inf

/- Remark 26.21.18 (2) and (3): the terminal-morphism criterion and pullback theorem specialize
to each of the four properties used in the source. -/
section QuasiSeparated

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
variable (hX : MorphismProperty.toTerminal @QuasiSeparated X)
variable (hY : MorphismProperty.toTerminal @QuasiSeparated Y)
variable (hZ : MorphismProperty.toTerminal @QuasiSeparated Z)

@[stacks 0816] #check MorphismProperty.mem_iff_toTerminal @QuasiSeparated f hY
@[stacks 0816] #check MorphismProperty.toTerminal_pullback @QuasiSeparated f g hX hY hZ

end QuasiSeparated

section Separated

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
variable (hX : MorphismProperty.toTerminal @IsSeparated X)
variable (hY : MorphismProperty.toTerminal @IsSeparated Y)
variable (hZ : MorphismProperty.toTerminal @IsSeparated Z)

@[stacks 0816] #check MorphismProperty.mem_iff_toTerminal @IsSeparated f hY
@[stacks 0816] #check MorphismProperty.toTerminal_pullback @IsSeparated f g hX hY hZ

end Separated

section QuasiCompactQuasiSeparated

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
variable (hX : MorphismProperty.toTerminal (@QuasiCompact ⊓ @QuasiSeparated) X)
variable (hY : MorphismProperty.toTerminal (@QuasiCompact ⊓ @QuasiSeparated) Y)
variable (hZ : MorphismProperty.toTerminal (@QuasiCompact ⊓ @QuasiSeparated) Z)

@[stacks 0816] #check MorphismProperty.mem_iff_toTerminal
  (@QuasiCompact ⊓ @QuasiSeparated) f hY
@[stacks 0816] #check MorphismProperty.toTerminal_pullback
  (@QuasiCompact ⊓ @QuasiSeparated) f g hX hY hZ

end QuasiCompactQuasiSeparated

section QuasiCompactSeparated

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
variable (hX : MorphismProperty.toTerminal (@QuasiCompact ⊓ @IsSeparated) X)
variable (hY : MorphismProperty.toTerminal (@QuasiCompact ⊓ @IsSeparated) Y)
variable (hZ : MorphismProperty.toTerminal (@QuasiCompact ⊓ @IsSeparated) Z)

@[stacks 0816] #check MorphismProperty.mem_iff_toTerminal
  (@QuasiCompact ⊓ @IsSeparated) f hY
@[stacks 0816] #check MorphismProperty.toTerminal_pullback
  (@QuasiCompact ⊓ @IsSeparated) f g hX hY hZ

end QuasiCompactSeparated
