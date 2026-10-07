module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Biterminal
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Cat.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift.Components
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift.Functoriality.Identity.Components
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift.Functoriality.Composition.Components
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoCone.Hom

/-!
# Conical bilimits in a bicategory

This is the umbrella module for the conical-bilimit API. The implementation is split by
mathematical responsibility:

* `Bilimit.Basic` owns pseudocones, their Yoneda-style universal property, selected
  `BilimitCone`s, and the corresponding existence predicates;
* `PseudoCone.Hom` exposes maps and `2`-morphisms between varying-apex pseudocones without a
  bilimit hypothesis;
* `Bilimit.Lift` and `Bilimit.Lift.Functoriality` provide chosen universal maps and their
  identity and composition comparisons, while their `Components` leaves expose vertexwise
  computations;
* `Bilimit.Equivalence` identifies the apices of two bilimit cones;
* `Bilimit.Biterminal` relates the represented universal property to biterminality in the
  locally groupoidal case;
* `Bilimit.Cat.Basic`, `Bilimit.Cat.Evaluation`, and `Bilimit.Cat.Cone` construct the
  canonical conical bilimit of a Cat-valued pseudodiagram.

Import a leaf module when only one layer is needed, or this module for the complete public
interface.
-/
