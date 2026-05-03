This Haskell implementation demonstrates a **Pure Type System (PTS)**—specifically a variant of the **Lambda Cube** (like the Calculus of Constructions)—using **De Bruijn Indices** for variable management.

Below is a breakdown of the core concepts and how the code functions.

---

## 1. Data Definition: The Syntax
The `Term` data type represents the building blocks of the language. Unlike standard lambda calculus, this system merges "terms" and "types" into a single structure.

*   **`Var Index`**: Uses **De Bruijn Indices** (integers) instead of names. `0` refers to the innermost binder, `1` to the next, and so on. This eliminates the "variable capture" problem during substitution.
*   **`Pi Name Term Term`**: Represents Dependent Types ($\Pi$-types). If the second `Term` doesn't use the bound variable, this acts like a standard function arrow ($A \to B$).
*   **`Kind (*)` and `Box (□)`**: These are the "Sorts."
    *   `Kind` is the type of types (like `Int` or `Bool`).
    *   `Box` is the type of `Kind`.

---

## 2. De Bruijn Index Management
Managing variables without names requires two helper operations: **Shifting** and **Substitution**.

### Shifting (`shift`)
When you move a term underneath a new binder (a `Lam` or `Pi`), its free variables must be incremented so they still point to the correct "outside" binders.
*   **`d`**: The amount to add.
*   **`c`**: The cutoff (only indices $\ge c$ are free variables that need shifting).

### Substitution (`substitute`)
This replaces a variable (index `j`) with a new term `n`. 
> **Note:** In the `Lam` and `Pi` cases, notice the `shift 1 0 n`. This is because as we descend into a binder, the context grows, so the free variables inside the term we are inserting must be adjusted.

---

## 3. Evaluation (Normalization)
The `reduce` function performs **$\beta$-reduction**.

```haskell
reduce (shift (-1) 0 (substitute 0 (shift 1 0 n) e))
```
When applying a function $(\lambda x. e)n$:
1.  We prepare $n$ by shifting it up.
2.  We substitute it into $e$ at index $0$.
3.  We **shift the whole result by -1**. This is crucial: since the $\lambda$ binder is now gone, all remaining free variables in $e$ must "move down" one level to stay correct.

---

## 4. The Type System (`typeOf`)
This is the heart of the logic. It follows the rules of the Lambda Cube.

| Rule | Explanation |
| :--- | :--- |
| **Sorts** | `Kind` has type `Box`. `Box` is the "top" and has no type. |
| **Variables** | Look up the type in the `ctx`. We shift the retrieved type because the variable is $i$ levels deep in the stack. |
| **Pi-Types** | A $\Pi$-type is valid only if its components are valid sorts (Types or Kinds). |
| **Abstraction** | To type check $\lambda x:A. e$, we assume $x$ has type $A$ and check the body $e$. The result is a $\Pi$-type. |
| **Application** | If $m$ is a function $(\Pi x:A. B)$ and $n$ has type $A$, the result is $B$ with $n$ substituted in. |

---

## 5. Walkthrough: Polymorphic Identity
In the `main` function, the code defines:
`λA:*. λx:A. x` $\rightarrow$ `Lam "A" Kind (Lam "x" (Var 0) (Var 0))`

1.  **Outer Lam ("A")**: Binds index 0 as `Kind`.
2.  **Inner Lam ("x")**: Binds a new index 0 as type `A` (which is now index 1).
3.  **Variable (Var 0)**: Refers to `x`.

**The result of `typeOf`**:
`ΠA:*. Πx:A. A`

### Why use De Bruijn Indices?
While they are harder for humans to read (e.g., `Var 0` vs `x`), they are perfect for computers because:
*   **Alpha-equivalence is trivial**: `λx.x` and `λy.y` both become `Lam 0`.
*   **No Name Clashes**: You never have to worry about "renaming" variables to avoid accidentally shadowing a global variable.

---

### Suggestions for Extension
If you want to make this code more powerful, you could:
1.  **Add a Parser**: Convert strings like `\A:*. \x:A. x` into the `Term` data type.
2.  **Add Constants**: Add `Nat` or `String` as primitive types.
3.  **Pretty Printer**: Write a function that converts De Bruijn indices back into human-readable names using the `Name` hints provided in the constructors.