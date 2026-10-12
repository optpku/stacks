/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import ReasLib.RingTheory.Extension.Cotangent.Naturality
import StacksCheckRecall

/-!
# Functoriality of cotangent presentations

@stack 00S1
-/

@[expose] public section

open Algebra
open Algebra.Generators
open Algebra.Extension

universe w w' w'' u v u' v' u'' v''

section General

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {R' : Type u'} {S' : Type v'} [CommRing R'] [CommRing S'] [Algebra R' S']
variable {R'' : Type u''} {S'' : Type v''} [CommRing R''] [CommRing S''] [Algebra R'' S'']
variable {ι : Type w} {ι' : Type w'} {ι'' : Type w''}

variable (P : Generators R S ι) (P' : Generators R' S' ι') (P'' : Generators R'' S'' ι'')

variable [Algebra S S']

/- Lemma 10.134.2 (1) is a `source-facing` existence claim whose canonical owner is
`Generators.defaultHom`. For two presentations in the commutative square, the distinguished
morphism of presentations is already provided upstream. -/
@[stacks 00S1 "(1)"]
#check (Generators.defaultHom P P' : P.Hom P')

variable [Algebra R R'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']

variable {P P'} (f g : P.Hom P')

/- Lemma 10.134.2 (2) is exactly the owner homotopy identity
`Extension.CotangentSpace.map_sub_map` applied to `f.toExtensionHom` and `g.toExtensionHom`. -/
@[stacks 00S1 "(2)"]
#check
  (Extension.CotangentSpace.map_sub_map (f.toExtensionHom) (g.toExtensionHom) :
    CotangentSpace.map f.toExtensionHom - CotangentSpace.map g.toExtensionHom =
      (let d := P'.toExtension.cotangentComplex
       d.restrictScalars S) ∘ₗ f.toExtensionHom.sub g.toExtensionHom)

/- Lemma 10.134.2 (3) is exactly the owner homotopy identity
`Extension.Cotangent.map_sub_map` applied to `f.toExtensionHom` and `g.toExtensionHom`. -/
@[stacks 00S1 "(3)"]
#check
  (Extension.Cotangent.map_sub_map (f.toExtensionHom) (g.toExtensionHom) :
    Cotangent.map f.toExtensionHom - Cotangent.map g.toExtensionHom =
      f.toExtensionHom.sub g.toExtensionHom ∘ₗ P.toExtension.cotangentComplex)

/- Lemma 10.134.2 (4) is the canonical presentation-independence theorem
`Extension.H1Cotangent.map_eq` specialized to presentation morphisms. -/
@[stacks 00S1 "(4)"]
#check
  (Extension.H1Cotangent.map_eq f.toExtensionHom g.toExtensionHom :
    Extension.H1Cotangent.map f.toExtensionHom = Extension.H1Cotangent.map g.toExtensionHom)

variable [Algebra S' S''] [Algebra S S'']
variable [Algebra R R''] [Algebra R' R''] [Algebra R' S''] [Algebra R S'']
variable [IsScalarTower R' R'' S''] [IsScalarTower R R'' S''] [IsScalarTower R R' R'']
variable [IsScalarTower R' S' S''] [IsScalarTower S S' S'']

variable {P''} (h : P'.Hom P'')

/- Lemma 10.134.2 (5) is the owner functoriality statement
`Extension.H1Cotangent.map_comp` specialized to presentation morphisms. -/
@[stacks 00S1 "(5)"]
#check
  (Extension.H1Cotangent.map_comp f.toExtensionHom h.toExtensionHom :
    Extension.H1Cotangent.map (h.toExtensionHom.comp f.toExtensionHom) =
      (Extension.H1Cotangent.map h.toExtensionHom).restrictScalars S ∘ₗ
        Extension.H1Cotangent.map f.toExtensionHom)

end General

section FixedBase

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type w} {ι' : Type w'}
variable (P : Generators R S ι) (P' : Generators R S ι')

/- Lemma 10.134.2 (6) is recalled canonically by `Generators.H1Cotangent.equiv`. -/
@[stacks 00S1 "(6)"]
#check
  (Generators.H1Cotangent.equiv P P' :
    P.toExtension.H1Cotangent ≃ₗ[S] P'.toExtension.H1Cotangent)

/- Lemma 10.134.2 (7) is recalled canonically by `Generators.equivH1Cotangent`. -/
@[stacks 00S1 "(7)"]
#check (P.equivH1Cotangent : P.toExtension.H1Cotangent ≃ₗ[S] H1Cotangent R S)

end FixedBase

/- Lemma 10.134.2 [stacks 00S1]: the canonical comparison with
`Algebra.H1Cotangent R S` is functorial in morphisms of presentations.  The
reusable owner is the neutral theorem in `ReasLib`. -/
@[stacks 00S1 "naturality"]
#check @Algebra.Generators.equivH1Cotangent_naturality
