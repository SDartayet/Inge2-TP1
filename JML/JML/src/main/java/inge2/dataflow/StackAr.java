package inge2.dataflow;

public class StackAr {

    //@ public invariant (-1 <= top < elems.length);
    /**
     * Capacidad por defecto de la pila.
     */

    //@ spec_public
    private final static int DEFAULT_CAPACITY = 10;

    /**
     * Arreglo que contiene los elementos de la pila.
     */
    //@ spec_public
    private final int[] elems;

    /**
     * Indice del tope de la pila.
     */

    //@ spec_public
    private int top = -1;

    //@ ensures top == -1 && elems.length == DEFAULT_CAPACITY;
    public StackAr() {
        this(DEFAULT_CAPACITY);
    }

    //@ requires capacity > 0;
    //@ ensures top == -1 && elems.length == capacity;
    public StackAr(int capacity) {
        this.elems = new int[capacity];
    }

    //@ ensures top == \old(top) && elems == \old(elems) && (\result == true <==> top == -1);
    public boolean isEmpty() {
        return top == -1;
    }

    //@ ensures top == \old(top) && elems == \old(elems) && (\result == true <==> top == elems.length - 1);
    public boolean isFull() {
        return top == elems.length - 1;
    }

    //@ ensures top == \old(top) && elems == \old(elems) && \result == top + 1;
    public int size() {
        return top + 1;
    }

    //@ requires top < elems.length -1;
    //@ ensures top == \old(top) + 1;
    //@ ensures elems[top] == o && (\forall int n; 0 <= n < top; elems[n] == \old(elems[n]));
    public void push(int o) {
        top++;
        elems[top] = o;
    }

    //@ requires top >= 0;
    //@ ensures top == \old(top) - 1 && \result == \old(elems[top]);
    //@ ensures \forall int n; 0 <= n <= top; elems[n] == \old(elems[n]);
    public int pop() {
        return elems[top--];
    }

    //@ requires top >= 0;
    //@ ensures top == \old(top) && \result == elems[top];
    //@ ensures \forall int n; 0 <= n <= top; elems[n] == \old(elems[n]);
    public int peek() {
        return elems[top];
    }
}

