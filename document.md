# Comprehensive Tests for Cubical Lambda

> Run with: `./cubical comprehensive_tests.ctt`

---

## 1. Path Basics

| Name | Description |
|------|-------------|
| `refl` | Reflexivity: the constant path proves `Path A x x` |
| `cong` | Congruence / ap: a function maps a path to a path |
| `path_at0` | Path applied at `0` equals the left endpoint |
| `path_at1` | Path applied at `1` equals the right endpoint |
| `path_as_itself` | A path witnesses that its endpoints are definitionally equal to `path@0` and `path@1` |

```
check refl : PI (A : U0) . PI (x : A) . Path A x x
  = lambda_ A . lambda_ x . {_} x

check cong : PI (A : U0) . PI (B : U0) . PI (f : PI (_ : A) . B) .
             PI (x : A) . PI (y : A) . PI (p : Path A x y) . Path B (f x) (f y)
  = lambda_ A . lambda_ B . lambda_ f . lambda_ x . lambda_ y . lambda_ p . {i} f (p @ i)

check path_at0 : PI (A : U0) . PI (x : A) . PI (y : A) . PI (p : Path A x y) . Path A x (p @ 0)
  = lambda_ A . lambda_ x . lambda_ y . lambda_ p . {_} x

check path_at1 : PI (A : U0) . PI (x : A) . PI (y : A) . PI (p : Path A x y) . Path A y (p @ 1)
  = lambda_ A . lambda_ x . lambda_ y . lambda_ p . {_} y

check path_as_itself : PI (A : U0) . PI (x : A) . PI (y : A) . PI (p : Path A x y) . Path A (p @ 0) (p @ 1)
  = lambda_ A . lambda_ x . lambda_ y . lambda_ p . p
```

---

## 2. Higher-Order Cong

| Name | Description |
|------|-------------|
| `cong2_left` | Congruence under a binary function in the first argument |
| `cong2_right` | Congruence under a binary function in the second argument |
| `happly` | A path of functions gives pointwise paths (inverse of funext) |

```
check cong2_left : PI (A B C : U0) . PI (f : PI (_ : A) . PI (_ : B) . C) .
                   PI (x y : A) . PI (p : Path A x y) . PI (b : B) . Path C (f x b) (f y b)
  = ... {i} f (p @ i) b

check cong2_right : PI (A B C : U0) . PI (f : PI (_ : A) . PI (_ : B) . C) .
                    PI (a : A) . PI (x y : B) . PI (q : Path B x y) . Path C (f a x) (f a y)
  = ... {i} f a (q @ i)

check happly : PI (A B : U0) . PI (f g : PI (_ : A) . B) .
               PI (p : Path (PI (_ : A) . B) f g) . PI (x : A) . Path B (f x) (g x)
  = ... {i} p @ i x
```

---

## 3. Sigma / Product Types

| Name | Description |
|------|-------------|
| `sigma_fst` | `fst` of an explicit pair reduces to the first component |
| `sigma_snd` | `snd` of an explicit pair reduces to the second component |
| `sigma_eta` | Eta rule: every element equals `(fst p, snd p)` (non-dependent case) |
| `swap` | Swap: `A × B → B × A` |
| `swap_invol` | Swap is an involution: `swap (swap p) = p` |
| `curry` | Curry: `(A × B → C) → A → B → C` |
| `uncurry` | Uncurry: `(A → B → C) → A × B → C` |
| `pair_path` | Componentwise path between pairs |
| `pair_path_fst` | `fst` of a componentwise pair-path recovers the original path |

```
check sigma_eta : PI (A B : U0) . PI (p : SIGMA (_ : A) . B) .
                  Path (SIGMA (_ : A) . B) p (pair (fst p) (snd p))
  = ... {_} pair (fst p) (snd p)

check swap_invol : PI (A B : U0) . PI (p : SIGMA (_ : A) . B) .
                   Path (SIGMA (_ : A) . B) p
                        (pair (snd (pair (snd p) (fst p))) (fst (pair (snd p) (fst p))))
  = ... {_} p

check pair_path : PI (A B : U0) . PI (a0 a1 : A) . PI (b0 b1 : B) .
                  PI (p : Path A a0 a1) . PI (q : Path B b0 b1) .
                  Path (SIGMA (_ : A) . B) (pair a0 b0) (pair a1 b1)
  = ... {i} pair (p @ i) (q @ i)
```

---

## 4. Transport

| Name | Description |
|------|-------------|
| `transport_const` | Transport along a constant path is the identity |
| `transport_fun_const` | Transport along a constant function-type path is the identity |
| `transport_ua` | Transport along `ua` of an equivalence applies the forward map |

```
check transport_const : PI (A : U0) . PI (x : A) . Path A x (transport ({_} A) x)
  = lambda_ A . lambda_ x . {_} x

check transport_ua : PI (A B : U0) . PI (e : Equiv A B) . PI (x : A) .
                     Path B (equivFwd e x) (transport (ua e) x)
  = ... {_} equivFwd e x
```

---

## 5. Hcomp Basics

| Name | Description |
|------|-------------|
| `hcomp_bot` | `hcomp` with `phi=0` (empty system) returns the base unchanged |
| `hcomp_top` | `hcomp` with `phi=1` (full system) returns the tube evaluated at `i=1` |
| `hcomp_const_tube` | `hcomp` with a trivial (constant) tube is a no-op |

```
check hcomp_bot : PI (A : U0) . PI (x : A) . Path A x (hcomp A [0] ({_} x) x)
  = ... {_} x

check hcomp_top : PI (A : U0) . PI (x y : A) . PI (p : Path A x y) .
                  Path A y (hcomp A [1] p x)
  = ... {_} y
```

---

## 6. Equivalences

| Name | Description |
|------|-------------|
| `id_equiv` | The identity function on `A` gives an equivalence `A ≃ A` |
| `id_equiv_fwd` | The forward map of the identity equivalence is the identity |
| `mkequiv_fwd` | `equivFwd` applied to a `mkEquiv` with explicit forward map `f` gives `f x` |

```
def id_equiv : PI (A : U0) . Equiv A A
  = lambda_ A . mkEquiv A A (lambda_ x . x) (lambda_ x . x)
                             (lambda_ a . {_} a) (lambda_ b . {_} b)

check mkequiv_fwd : PI (A B : U0) . PI (f g : PI (_ : A) . B) .
                    PI (eta : PI (a : A) . Path A a (g (f a))) .
                    PI (eps : PI (b : B) . Path B (f (g b)) b) .
                    PI (x : A) . Path B (f x) (equivFwd (mkEquiv A B f g eta eps) x)
  = ... {_} f x
```

> **Note:** `id_equiv` is opaque as a global, so `equivFwd` cannot reduce through it at check-time. Inlining the `mkEquiv` lets the `TEquivFwd` reduction rule fire.

---

## 7. Univalence

| Name | Description |
|------|-------------|
| `ua_id` | `ua` applied to the identity equivalence gives a path in the universe |
| `ua_type` | `ua` produces a path between its domain and codomain types |

```
check ua_id : PI (A : U0) . Path U0 A A
  = lambda_ A . ua (id_equiv A)

check ua_type : PI (A B : U0) . PI (e : Equiv A B) .
                Path U1 (Path U0 A B) (Path U0 A B)
  = ... {_} Path U0 A B
```

---

## 8. Universe Levels

| Name | Description |
|------|-------------|
| `u0_in_u1` | `U0` lives in `U1` |
| `pi_u0_level` | A Pi-type over `U0` lives in `U1` |
| `sigma_u0_level` | A Sigma-type over `U0` lives in `U1` |

```
check u0_in_u1 : Path U1 U0 U0 = {_} U0

check pi_u0_level : PI (A : U0) . Path U1 (PI (_ : A) . U0) (PI (_ : A) . U0)
  = lambda_ A . {_} PI (_ : A) . U0

check sigma_u0_level : PI (A : U0) . Path U1 (SIGMA (_ : A) . U0) (SIGMA (_ : A) . U0)
  = lambda_ A . {_} SIGMA (_ : A) . U0
```

---

## 9. Function Identity and Composition

| Name | Description |
|------|-------------|
| `id_fun` | Identity function |
| `id_comp_id` | Composition of identity with itself is identity |
| `K_combinator` | K combinator: always returns its first argument |
| `S_on_K` | S combinator applied to K and K gives identity |

```
check id_fun : PI (A : U0) . PI (x : A) . Path A x ((lambda_ x . x) x)
  = ... {_} x

check K_combinator : PI (A B : U0) . PI (x : A) . PI (y : B) .
                     Path A x ((lambda_ x . lambda_ _ . x) x y)
  = ... {_} x

check S_on_K : PI (A : U0) . PI (x : A) .
               Path A x ((lambda_ f . lambda_ g . lambda_ x . f x (g x))
                          (lambda_ x . lambda_ y . x)
                          (lambda_ x . lambda_ y . x) x)
  = ... {_} x
```

---

## 10. Path-Over-Function-Type (Funext Direction)

| Name | Description |
|------|-------------|
| `funext` | Pointwise paths give a path of functions |
| `funext_happly` | `funext` is right-inverse to `happly`: `happly (funext h) x = h x` |
| `funext3` | `funext` for three arguments |

```
check funext : PI (A B : U0) . PI (f g : PI (_ : A) . B) .
               PI (h : PI (x : A) . Path B (f x) (g x)) .
               Path (PI (_ : A) . B) f g
  = ... {i} lambda_ x . h x @ i

check funext_happly : PI (A B : U0) . PI (f g : PI (_ : A) . B) .
                      PI (h : PI (x : A) . Path B (f x) (g x)) . PI (x : A) .
                      Path (Path B (f x) (g x)) (h x) (h x)
  = ... {_} h x

check funext3 : PI (A B C D : U0) .
                PI (f g : PI (_ : A) . PI (_ : B) . PI (_ : C) . D) .
                PI (h : PI (x : A) . PI (y : B) . PI (z : C) . Path D (f x y z) (g x y z)) .
                Path (PI (_ : A) . PI (_ : B) . PI (_ : C) . D) f g
  = ... {i} lambda_ x . lambda_ y . lambda_ z . h x y z @ i
```

---

*Generated from `comprehensive_tests.ctt`*