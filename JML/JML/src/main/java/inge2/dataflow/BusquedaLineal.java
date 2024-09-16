package inge2.dataflow;

public class BusquedaLineal {

    // Busca un elemento en un arreglo de enteros.
    //@ requires true;
    //@ ensures \result == true <==> (\exists int n; 0 <= n < arr.length; arr[n] == elem);
    public static boolean busquedaLineal(int elem, int[] arr) {
        boolean result = false;

        //@ maintaining 0 <= i <= arr.length;
        //@ decreases arr.length - i;
        //@ loop_writes result, i;
        //@ maintaining result == true <==> (\exists int n; 0 <= n < i; arr[n] == elem);
        for (int i = 0; i < arr.length; i++) {
            if (elem == arr[i]) {
                result = true;
            }
        }

        return result;
    }
}