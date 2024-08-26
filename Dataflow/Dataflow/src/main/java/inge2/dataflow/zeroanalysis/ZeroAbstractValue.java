package inge2.dataflow.zeroanalysis;

/**
 * This enum represents the possible values of the zero analysis for a variable.
 */
public enum ZeroAbstractValue {

    /**
     * We don't have information about the variable.
     */
    BOTTOM("bottom"),

    /**
     * The variable is not zero.
     */
    NOT_ZERO("not-zero"),

    /**
     * The variable is zero.
     */
    ZERO("zero"),

    /**
     * The variable may be (or not) zero.
     */
    MAYBE_ZERO("maybe-zero");

    /**
     * The name of the ZeroAbstractValue.
     */
    private final String name;

    @Override
    public String toString() {
        return this.name;
    }

    ZeroAbstractValue(String name) {
        this.name = name;
    }

    /**
     * Returns the result of the addition between this ZeroAbstractValue and another.
     * @param another the other ZeroAbstractValue.
     * @return the result of the addition.
     */
    public ZeroAbstractValue add(ZeroAbstractValue another) {
        if (this == BOTTOM) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return BOTTOM;
            if (another == ZERO) return BOTTOM;
            if (another == MAYBE_ZERO) return BOTTOM;
        }
        if (this == NOT_ZERO) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return MAYBE_ZERO;
            if (another == MAYBE_ZERO) return MAYBE_ZERO;
            if (another == ZERO) return NOT_ZERO;
        }
        if (this == ZERO) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return NOT_ZERO;
            if (another == MAYBE_ZERO) return MAYBE_ZERO;
            if (another == ZERO) return ZERO;
        }
        if (this == MAYBE_ZERO) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return MAYBE_ZERO;
            if (another == MAYBE_ZERO) return MAYBE_ZERO;
            if (another == ZERO) return MAYBE_ZERO;
        }

        throw new UnsupportedOperationException();
    }

    /**
     * Returns the result of the division between this ZeroAbstractValue and another.
     * @param another the other ZeroAbstractValue.
     * @return the result of the division.
     */
    public ZeroAbstractValue divideBy(ZeroAbstractValue another) {
        if (this == BOTTOM) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return BOTTOM;
            if (another == ZERO) return BOTTOM;
            if (another == MAYBE_ZERO) return BOTTOM;
        }
        if (this == NOT_ZERO) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return MAYBE_ZERO;
            if (another == MAYBE_ZERO) return MAYBE_ZERO;
            if (another == ZERO) return BOTTOM;
        }
        if (this == ZERO) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return ZERO;
            if (another == MAYBE_ZERO) return ZERO;
            if (another == ZERO) return BOTTOM;
        }
        if (this == MAYBE_ZERO) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return MAYBE_ZERO;
            if (another == MAYBE_ZERO) return MAYBE_ZERO;
            if (another == ZERO) return BOTTOM;
        }
        return null;
    }

    /**
     * Returns the result of the multiplication between this ZeroAbstractValue and another.
     * @param another the other ZeroAbstractValue.
     * @return the result of the multiplication.
     */
    public ZeroAbstractValue multiplyBy(ZeroAbstractValue another) {
        if (this == BOTTOM) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return BOTTOM;
            if (another == ZERO) return BOTTOM;
            if (another == MAYBE_ZERO) return BOTTOM;
        }
        if (this == NOT_ZERO) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return NOT_ZERO;
            if (another == MAYBE_ZERO) return MAYBE_ZERO;
            if (another == ZERO) return ZERO;
        }
        if (this == ZERO) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return ZERO;
            if (another == MAYBE_ZERO) return ZERO;
            if (another == ZERO) return ZERO;
        }
        if (this == MAYBE_ZERO) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return MAYBE_ZERO;
            if (another == MAYBE_ZERO) return MAYBE_ZERO;
            if (another == ZERO) return ZERO;
        }
        return null;
    }

    /**
     * Returns the result of the subtraction between this ZeroAbstractValue and another.
     * @param another the other ZeroAbstractValue.
     * @return the result of the subtraction.
     */
    public ZeroAbstractValue subtract(ZeroAbstractValue another) {
        if (this == BOTTOM) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return BOTTOM;
            if (another == ZERO) return BOTTOM;
            if (another == MAYBE_ZERO) return BOTTOM;
        }
        if (this == NOT_ZERO) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return MAYBE_ZERO;
            if (another == MAYBE_ZERO) return MAYBE_ZERO;
            if (another == ZERO) return NOT_ZERO;
        }
        if (this == ZERO) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return NOT_ZERO;
            if (another == MAYBE_ZERO) return MAYBE_ZERO;
            if (another == ZERO) return ZERO;
        }
        if (this == MAYBE_ZERO) {
            if (another == BOTTOM) return BOTTOM;
            if (another == NOT_ZERO) return MAYBE_ZERO;
            if (another == MAYBE_ZERO) return MAYBE_ZERO;
            if (another == ZERO) return MAYBE_ZERO;
        }
        return null;
    }

    /**
     * Returns the result of the merge between this ZeroAbstractValue and another.
     * @param another the other ZeroAbstractValue.
     * @return the result of the merge.
     */
    public ZeroAbstractValue merge(ZeroAbstractValue another) {
        if (this == MAYBE_ZERO || another == MAYBE_ZERO) return MAYBE_ZERO;
        if (this == BOTTOM || another == BOTTOM) {
            if (another == BOTTOM) return this;
            else return another;
        }
        if (this == another) return this;
        else return MAYBE_ZERO;
    }

}
