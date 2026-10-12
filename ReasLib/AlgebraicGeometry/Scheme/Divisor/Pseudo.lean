/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NonvanishingLocus
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections.Open
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Pseudo-divisors on schemes

A pseudo-divisor consists of an invertible module, a closed support, and a nowhere-vanishing
section on the complement of that support.
-/

@[expose] public section

open CategoryTheory Opposite Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A pseudo-divisor on a scheme is an invertible module together with a closed subset and a
nowhere-vanishing section on its open complement. -/
structure PseudoDivisor (X : Scheme.{u}) where
  /-- The invertible module underlying the pseudo-divisor. -/
  lineBundle : X.Modules
  /-- The closed subset outside which the pseudo-divisor is trivialized. -/
  support : TopologicalSpace.Closeds X
  /-- The section on the open complement of the support. -/
  section_ : (Modules.restrict lineBundle (Scheme.Opens.ι support.compl)).sections
  /-- The underlying module is invertible. -/
  invertible : Modules.Invertible lineBundle
  /-- The section is nowhere vanishing on the open complement. -/
  nowhereVanishing :
    RingedSpace.sectionNonvanishingLocus
      (Scheme.Opens.toScheme support.compl).toRingedSpace
      (Modules.restrict lineBundle (Scheme.Opens.ι support.compl)) section_ = Set.univ

namespace PseudoDivisor

/-- Construct a pseudo-divisor from its line bundle, closed support, complement section, and
the two defining properties. -/
def ofSection {X : Scheme.{u}} (lineBundle : X.Modules)
    (support : TopologicalSpace.Closeds X)
    (section_ : (Modules.restrict lineBundle (Scheme.Opens.ι support.compl)).sections)
    (invertible : Modules.Invertible lineBundle)
    (nowhereVanishing :
      RingedSpace.sectionNonvanishingLocus
        (Scheme.Opens.toScheme support.compl).toRingedSpace
        (Modules.restrict lineBundle (Scheme.Opens.ι support.compl)) section_ = Set.univ) :
    PseudoDivisor X where
  lineBundle := lineBundle
  support := support
  section_ := section_
  invertible := invertible
  nowhereVanishing := nowhereVanishing

/-- The constructor for a pseudo-divisor records exactly the supplied line bundle, support,
section, invertibility, and nowhere-vanishing condition. -/
theorem ofSection_spec {X : Scheme.{u}} (lineBundle : X.Modules)
    (support : TopologicalSpace.Closeds X)
    (section_ : (Modules.restrict lineBundle (Scheme.Opens.ι support.compl)).sections)
    (invertible : Modules.Invertible lineBundle)
    (nowhereVanishing :
      RingedSpace.sectionNonvanishingLocus
        (Scheme.Opens.toScheme support.compl).toRingedSpace
        (Modules.restrict lineBundle (Scheme.Opens.ι support.compl)) section_ = Set.univ) :
    ofSection lineBundle support section_ invertible nowhereVanishing =
      { lineBundle := lineBundle
        support := support
        section_ := section_
        invertible := invertible
        nowhereVanishing := nowhereVanishing } := sorry

/-- The restriction of a global section to the complement of its zero support is nowhere
vanishing. -/
theorem globalSectionRestriction_nowhereVanishing {X : Scheme.{u}}
    (lineBundle : X.Modules) [Modules.Invertible lineBundle]
    (section_ : lineBundle.sections) :
    RingedSpace.sectionNonvanishingLocus
        (Scheme.Opens.toScheme
          (Scheme.zeroIdealSheaf lineBundle section_).support.compl).toRingedSpace
        (Modules.restrict lineBundle
          (Scheme.Opens.ι (Scheme.zeroIdealSheaf lineBundle section_).support.compl))
        (RingedSpace.sectionFromTop
          (Modules.restrict lineBundle
            (Scheme.Opens.ι (Scheme.zeroIdealSheaf lineBundle section_).support.compl))
          ((Modules.globalSectionsRestrict
            (Scheme.zeroIdealSheaf lineBundle section_).support.compl lineBundle).hom
              (section_.1 (Opposite.op ⊤)))) =
      Set.univ := sorry

/-- The pseudo-divisor determined by a global section and its zero support. -/
noncomputable def ofGlobalSection {X : Scheme.{u}} (lineBundle : X.Modules)
    [Modules.Invertible lineBundle] (section_ : lineBundle.sections) : PseudoDivisor X :=
  ofSection lineBundle (Scheme.zeroIdealSheaf lineBundle section_).support
    (RingedSpace.sectionFromTop
      (Modules.restrict lineBundle
        (Scheme.Opens.ι (Scheme.zeroIdealSheaf lineBundle section_).support.compl))
      ((Modules.globalSectionsRestrict
        (Scheme.zeroIdealSheaf lineBundle section_).support.compl lineBundle).hom
          (section_.1 (Opposite.op ⊤))))
    inferInstance (globalSectionRestriction_nowhereVanishing lineBundle section_)

/-- The pseudo-divisor of a global section has the section's zero support. -/
theorem ofGlobalSection_support {X : Scheme.{u}} (lineBundle : X.Modules)
    [Modules.Invertible lineBundle] (section_ : lineBundle.sections) :
    (ofGlobalSection lineBundle section_).support =
      (Scheme.zeroIdealSheaf lineBundle section_).support := sorry

end PseudoDivisor

end AlgebraicGeometry.Scheme
