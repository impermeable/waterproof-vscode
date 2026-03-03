/**
 * Type that indicates that the server is busy processing a document.
 */
export type Busy = {
    /** Status */
    status: "Busy";
    /** Extra metadata, can be used to communicate what the server is currently processing */
    metadata: string;
}

/**
 * Type that indicates that the server is idle. This means that it has 
 * either completed checking or is stopped.
 */
export type Idle = {
    status: "Idle" | "Stopped";
}

export type ServerStatus = Busy | Idle;
