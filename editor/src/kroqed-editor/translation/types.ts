import { Fragment, Node, Slice } from "prosemirror-model";

// Exports
export type NodeSerializer = (node: Node) => string;
export type MarkSerializer = (text: string) => string;


/**
 * Abstract class that describes a serializer for the conversion of the document
 */
export abstract class Serializer {

	// Two abstract methods that require implementation
    abstract serializeFragment(fragment: Fragment): string;
    abstract serializeSlice(slice: Slice): string;

	// Abstract method which serializes a slice
    serialize(input: Fragment | Slice) {

		// Check what format the input is from
        if (input instanceof Fragment) {

			// If input is a fragment we run the fragment serializer
			return this.serializeFragment(input);
		} else if (input instanceof Slice) {

			// If input is a slice we run the slice serializer
			return this.serializeSlice(input);
		} else {

			// Else we do not convert the input
			return null;
		}
    }
}